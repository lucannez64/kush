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

/// Ask the compiler which files the runtime source includes.
fn include_graph(compiler: &Path, source: &Path, defines: &[String]) -> Option<Vec<PathBuf>> {
    // Dependency scanning preprocesses only; it emits no object.
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
    Some(paths)
}

fn compiler_identity(
    compiler: &Path,
    source: &Path,
    defines: &[String],
    cheap_probes: bool,
    remembered_graph: Option<(&Path, &str)>,
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
    // Compiler wrappers can depend on arbitrary environment variables. Hash the
    // complete environment rather than persisting possible credential values.
    let mut environment: Vec<_> = std::env::vars_os().collect();
    environment.sort();
    let mut hash = DefaultHasher::new();
    environment.hash(&mut hash);
    identity.extend_from_slice(&hash.finish().to_le_bytes());
    // The include graph, including system headers, prevents a warm hit after
    // a libc/header upgrade or include-path change. The LLVM flavour
    // remembers the graph per compiler, flags, environment and runtime
    // source, and then only stats the listed headers: asking clang again
    // costs more than the rest of the lookup. A change to any listed header
    // is still seen; a new header that shadows a listed one is not, until
    // something else in that key changes.
    let graph_file = remembered_graph.map(|(root, runtime)| {
        let mut key = identity.clone();
        key.extend_from_slice(runtime.as_bytes());
        key.extend_from_slice(format!("{defines:?}").as_bytes());
        root.join(format!("{:016x}.graph", digest(&key)))
    });
    let remembered = graph_file.as_ref().and_then(|file| {
        let text = fs::read_to_string(file).ok()?;
        let paths: Vec<PathBuf> = text.lines().map(PathBuf::from).collect();
        (!paths.is_empty()
            && paths
                .iter()
                .all(|path| path.is_absolute() && path.is_file()))
        .then_some(paths)
    });
    let paths = match remembered {
        Some(paths) => paths,
        None => {
            let paths = include_graph(compiler, source, defines)?;
            let listed: Vec<&PathBuf> = paths.iter().filter(|path| *path != source).collect();
            if let Some(file) = &graph_file
                && let Some(root) = file.parent()
                && listed.iter().all(|path| {
                    path.is_absolute() && path.to_str().is_some_and(|p| !p.contains('\n'))
                })
            {
                // Published atomically, like cache entries.
                let _ = (|| -> std::io::Result<()> {
                    let stage = Scratch::new(root)
                        .map_err(|_| std::io::Error::other("cache staging failed"))?;
                    let temporary = stage.path().join("graph");
                    let text: String = listed
                        .iter()
                        .map(|path| format!("{}\n", path.display()))
                        .collect();
                    fs::write(&temporary, text)?;
                    fs::rename(temporary, file)
                })();
            }
            paths
        }
    };
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

/// Publish one cache entry atomically. A private staging directory makes this
/// safe for parallel compiler processes; an existing entry is never opened
/// or truncated. Best effort: a failure only means a later cold build.
fn publish(entry: &Path, key: &[u8], bytes: &[u8]) {
    let Some(root) = entry.parent() else {
        return;
    };
    let _ = (|| -> std::io::Result<()> {
        let stage =
            Scratch::new(root).map_err(|_| std::io::Error::other("cache staging failed"))?;
        let temporary = stage.path().join("entry");
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)?;
        file.write_all(key)?;
        file.write_all(&digest(bytes).to_le_bytes())?;
        file.write_all(bytes)?;
        file.sync_all()?;
        fs::rename(temporary, entry)
    })();
}

fn run(command: &mut Command, compiler: &Path) -> Result<()> {
    let output = command.output().map_err(|e| {
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
    Ok(())
}

pub(super) fn compile(runtime: &str, defines: &[String], scratch: &Scratch) -> Result<PathBuf> {
    let compiler = Path::new("cc");
    let object = scratch.path().join("runtime.o");
    let source = scratch.path().join("runtime.c");
    fs::write(&source, runtime).map_err(error)?;
    let directory = cache_directory(scratch);
    let identity = directory
        .as_ref()
        .and_then(|_| compiler_identity(compiler, &source, defines, true, None));
    let cache = directory.zip(identity);
    let mut key = b"kush-c-runtime-v1\0-std=c11\0-O2\0".to_vec();
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
    run(
        Command::new(compiler)
            .args(["-std=c11", "-O2"])
            .args(defines)
            .arg("-c")
            .arg(&source)
            .arg("-o")
            .arg(&object),
        compiler,
    )?;
    if let Some(entry) = entry
        && let Ok(bytes) = fs::read(&object)
    {
        publish(&entry, &key, &bytes);
    }
    Ok(object)
}

/// The runtime prepared for the LLVM backend.
pub(super) struct LlvmRuntime {
    /// Target description and the signature line of every runtime function.
    pub interface: String,
    /// The runtime object to link. Its formerly internal symbols are hidden
    /// instead, so inlined copies of runtime code can refer to them.
    pub object: PathBuf,
    /// Bitcode holding every runtime definition as `available_externally`:
    /// bodies LLVM may inline but never emits.
    pub inline: PathBuf,
}

/// Compile the runtime once with clang and derive the three artifacts of
/// [`LlvmRuntime`] from that single LLVM module, so the object and the
/// inlinable bodies cannot disagree. Each is cached under its own key.
pub(super) fn compile_llvm(
    runtime: &str,
    defines: &[String],
    scratch: &Scratch,
    clang: &Path,
) -> Result<LlvmRuntime> {
    let source = scratch.path().join("runtime.c");
    fs::write(&source, runtime).map_err(error)?;
    let directory = cache_directory(scratch);
    let identity = directory.as_ref().and_then(|root| {
        compiler_identity(
            clang,
            &source,
            defines,
            false,
            Some((root.as_path(), runtime)),
        )
    });
    let cache = directory.zip(identity);
    let entry = |artifact: &str| {
        let mut key =
            format!("kush-c-runtime-llvm-v3\0{artifact}\0-std=c11\0-O2\0-fPIC\0").into_bytes();
        key.extend_from_slice(runtime.as_bytes());
        key.extend_from_slice(format!("{defines:?}").as_bytes());
        if let Some((_, identity)) = &cache {
            key.extend_from_slice(identity);
        }
        let path = cache
            .as_ref()
            .map(|(root, _)| root.join(format!("{:016x}.cache", digest(&key))));
        (path, key)
    };
    let artifacts = [entry("interface"), entry("object"), entry("inline")];
    let object = scratch.path().join("runtime.o");
    let inline = scratch.path().join("runtime-inline.bc");
    let cached: Option<Vec<Vec<u8>>> = artifacts
        .iter()
        .map(|(path, key)| path.as_ref().and_then(|path| read_entry(path, key)))
        .collect();
    if let Some(cached) = cached
        && let Ok(interface) = String::from_utf8(cached[0].clone())
    {
        fs::write(&object, &cached[1]).map_err(error)?;
        fs::write(&inline, &cached[2]).map_err(error)?;
        return Ok(LlvmRuntime {
            interface,
            object,
            inline,
        });
    }
    let module = scratch.path().join("runtime.ll");
    run(
        Command::new(clang)
            .args(["-std=c11", "-O2"])
            .args(defines)
            // Position-independent like the Cranelift program object.
            .args(["-fPIC", "-S", "-emit-llvm"])
            .arg(&source)
            .arg("-o")
            .arg(&module),
        clang,
    )?;
    let text = fs::read_to_string(&module).map_err(error)?;
    let split = super::llvm::split_runtime(&text)
        .ok_or_else(|| error("the LLVM backend does not understand this clang's runtime module"))?;
    let exported = scratch.path().join("runtime-export.ll");
    let inlinable = scratch.path().join("runtime-inline.ll");
    fs::write(&exported, &split.exported).map_err(error)?;
    fs::write(&inlinable, &split.inlinable).map_err(error)?;
    run(
        Command::new(clang)
            .args(["-O2", "-fPIC", "-c", "-Wno-override-module"])
            .arg(&exported)
            .arg("-o")
            .arg(&object),
        clang,
    )?;
    // A plain format conversion: no optimization level, no passes.
    run(
        Command::new(clang)
            .args(["-x", "ir", "-c", "-emit-llvm", "-Wno-override-module"])
            .arg(&inlinable)
            .arg("-o")
            .arg(&inline),
        clang,
    )?;
    let outputs = [
        split.interface.clone().into_bytes(),
        fs::read(&object).map_err(error)?,
        fs::read(&inline).map_err(error)?,
    ];
    for ((path, key), bytes) in artifacts.iter().zip(&outputs) {
        if let Some(path) = path {
            publish(path, key, bytes);
        }
    }
    Ok(LlvmRuntime {
        interface: split.interface,
        object,
        inline,
    })
}
