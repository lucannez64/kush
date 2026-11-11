//! Private, best-effort cache for the C runtime. Entries are published atomically;
//! callers always link a scratch-local copy, never a mutable shared object.
use super::{Result, Scratch, error};
use std::{
    collections::hash_map::DefaultHasher,
    fs,
    hash::{Hash, Hasher},
    io::{Read, Write},
    path::{Path, PathBuf},
    process::Command,
};

fn digest(bytes: &[u8]) -> u64 {
    let mut hash = DefaultHasher::new();
    bytes.hash(&mut hash);
    hash.finish()
}

fn compiler_identity(
    compiler: &Path,
    source: &Path,
    defines: &[String],
    cheap_probes: bool,
) -> Option<Vec<u8>> {
    let path = if compiler.components().count() > 1 {
        compiler.to_path_buf()
    } else {
        std::env::split_paths(&std::env::var_os("PATH")?)
            .map(|directory| directory.join(compiler))
            .find(|path| path.is_file())?
    };
    let path = fs::canonicalize(path).ok()?;
    let metadata = fs::metadata(&path).ok()?;
    let mut identity = format!(
        "{path:?}:{:?}:{}",
        metadata.modified().ok()?,
        metadata.len()
    )
    .into_bytes();
    // A clang start costs about ten times a gcc start. For the LLVM flavour
    // the binary's identity above, the include graph below (its paths name
    // the versioned resource directory) and the environment hash already pin
    // the compiler, so the two extra probes are skipped.
    let probes: &[&str] = if cheap_probes {
        &["--version", "-dumpmachine"]
    } else {
        &[]
    };
    for argument in probes {
        let output = Command::new(compiler).arg(argument).output().ok()?;
        if !output.status.success() {
            return None;
        }
        identity.extend_from_slice(&output.stdout);
        identity.extend_from_slice(&output.stderr);
    }
    identity.extend_from_slice(format!("{:?}", std::env::current_dir().ok()?).as_bytes());
    // Ask this compiler for its real include graph, including system headers.
    // This prevents a warm hit after a libc/header upgrade or include-path
    // change. Dependency scanning preprocesses only; it emits no object.
    let dependencies = Command::new(compiler)
        .args(["-std=c11", "-O2"])
        .args(defines)
        .args(["-M", "-MT", "kush_runtime"])
        .arg(source)
        .output()
        .ok()?;
    if !dependencies.status.success() {
        return None;
    }
    let dependencies = String::from_utf8(dependencies.stdout).ok()?;
    let (_, dependencies) = dependencies.split_once(':')?;
    let mut paths = Vec::new();
    let mut path = String::new();
    let mut escaped = false;
    for character in dependencies.chars() {
        if escaped {
            if character != '\n' {
                path.push(character);
            }
            escaped = false;
        } else if character == '\\' {
            escaped = true;
        } else if character.is_whitespace() {
            if !path.is_empty() {
                paths.push(PathBuf::from(std::mem::take(&mut path)));
            }
        } else {
            path.push(character);
        }
    }
    if !path.is_empty() {
        paths.push(PathBuf::from(path));
    }
    if escaped || paths.is_empty() {
        return None;
    }
    for path in paths {
        if path == source {
            continue;
        }
        let metadata = fs::metadata(&path).ok()?;
        identity.extend_from_slice(
            format!(
                "{path:?}:{:?}:{}",
                metadata.modified().ok()?,
                metadata.len()
            )
            .as_bytes(),
        );
    }
    // Compiler wrappers can depend on arbitrary environment variables. Hash the
    // complete environment rather than persisting possible credential values.
    let mut environment: Vec<_> = std::env::vars_os().collect();
    environment.sort();
    let mut hash = DefaultHasher::new();
    environment.hash(&mut hash);
    identity.extend_from_slice(&hash.finish().to_le_bytes());
    Some(identity)
}

fn cache_directory(scratch: &Scratch) -> Option<PathBuf> {
    if std::env::var_os("KUSH_NO_RUNTIME_CACHE").is_some() {
        return None;
    }
    let root = if let Some(root) = std::env::var_os("KUSH_RUNTIME_CACHE") {
        PathBuf::from(root)
    } else if let Some(root) = std::env::var_os("XDG_CACHE_HOME") {
        PathBuf::from(root).join("kush/native-runtime-v1")
    } else {
        PathBuf::from(std::env::var_os("HOME")?).join(".cache/kush/native-runtime-v1")
    };
    // Refuse symlink components. Unusable/untrusted caches simply compile cold.
    for ancestor in root.ancestors() {
        if fs::symlink_metadata(ancestor).is_ok_and(|m| m.file_type().is_symlink()) {
            return None;
        }
    }
    let mut builder = fs::DirBuilder::new();
    builder.recursive(true);
    #[cfg(unix)]
    {
        use std::os::unix::fs::DirBuilderExt;
        builder.mode(0o700);
    }
    builder.create(&root).ok()?;
    let metadata = fs::symlink_metadata(&root).ok()?;
    if !metadata.is_dir() {
        return None;
    }
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        if metadata.mode() & 0o077 != 0
            || metadata.uid() != fs::metadata(scratch.path()).ok()?.uid()
        {
            return None;
        }
    }
    Some(root)
}

fn read_entry(path: &Path, key: &[u8]) -> Option<Vec<u8>> {
    let metadata = fs::symlink_metadata(path).ok()?;
    if !metadata.is_file() || metadata.len() > 64 * 1024 * 1024 {
        return None;
    }
    let mut bytes = Vec::new();
    fs::File::open(path)
        .ok()?
        .take(64 * 1024 * 1024)
        .read_to_end(&mut bytes)
        .ok()?;
    if !bytes.starts_with(key) {
        return None;
    }
    let tail = bytes.get(key.len()..)?;
    let (checksum, object) = tail.split_at_checked(8)?;
    if checksum != digest(object).to_le_bytes() || object.is_empty() {
        return None;
    }
    Some(object.to_vec())
}

pub(super) fn compile(runtime: &str, defines: &[String], scratch: &Scratch) -> Result<PathBuf> {
    compile_as(runtime, defines, scratch, Path::new("cc"), Output::Object)
}

/// The runtime as textual LLVM IR, for whole-program optimization by the LLVM
/// backend. Cached exactly like the object, under a distinct key.
pub(super) fn compile_llvm_ir(
    runtime: &str,
    defines: &[String],
    scratch: &Scratch,
    clang: &Path,
) -> Result<PathBuf> {
    compile_as(runtime, defines, scratch, clang, Output::LlvmIr)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Output {
    Object,
    LlvmIr,
}

fn compile_as(
    runtime: &str,
    defines: &[String],
    scratch: &Scratch,
    compiler: &Path,
    kind: Output,
) -> Result<PathBuf> {
    let object = scratch.path().join(match kind {
        Output::Object => "runtime.o",
        Output::LlvmIr => "runtime.ll",
    });
    let source = scratch.path().join("runtime.c");
    fs::write(&source, runtime).map_err(error)?;
    let directory = cache_directory(scratch);
    let identity = directory
        .as_ref()
        .and_then(|_| compiler_identity(compiler, &source, defines, kind == Output::Object));
    let cache = directory.zip(identity);
    let mut key = match kind {
        Output::Object => b"kush-c-runtime-v1\0-std=c11\0-O2\0".to_vec(),
        Output::LlvmIr => b"kush-c-runtime-llvm-ir-v1\0-std=c11\0-O2\0".to_vec(),
    };
    key.extend_from_slice(runtime.as_bytes());
    key.extend_from_slice(format!("{defines:?}").as_bytes());
    if let Some((_, identity)) = &cache {
        key.extend_from_slice(identity);
    }
    let entry = cache
        .as_ref()
        .map(|(root, _)| root.join(format!("{:016x}.cache", digest(&key))));
    if let Some(bytes) = entry.as_ref().and_then(|path| read_entry(path, &key)) {
        fs::write(&object, bytes).map_err(error)?;
        return Ok(object);
    }
    let mut command = Command::new(compiler);
    command.args(["-std=c11", "-O2"]).args(defines);
    match kind {
        Output::Object => command.arg("-c"),
        // Position-independent like the Cranelift program object.
        Output::LlvmIr => command.args(["-fPIC", "-S", "-emit-llvm"]),
    };
    let output = command
        .arg(&source)
        .arg("-o")
        .arg(&object)
        .output()
        .map_err(|e| {
            error(format!(
                "could not start the native C compiler '{}': {e}",
                compiler.display()
            ))
        })?;
    if !output.status.success() {
        return Err(error(format!(
            "native runtime compilation failed: {}",
            String::from_utf8_lossy(&output.stderr)
        )));
    }
    if let Some(entry) = entry {
        // A private staging directory makes publication atomic even for parallel
        // compiler processes. Never open/truncate an existing cache entry.
        if let Some(root) = entry.parent() {
            let _ = (|| -> std::io::Result<()> {
                let stage = Scratch::new(root)
                    .map_err(|_| std::io::Error::other("cache staging failed"))?;
                let bytes = fs::read(&object)?;
                let temporary = stage.path().join("entry");
                let mut file = fs::OpenOptions::new()
                    .write(true)
                    .create_new(true)
                    .open(&temporary)?;
                file.write_all(&key)?;
                file.write_all(&digest(&bytes).to_le_bytes())?;
                file.write_all(&bytes)?;
                file.sync_all()?;
                fs::rename(temporary, &entry)
            })();
        }
    }
    Ok(object)
}
