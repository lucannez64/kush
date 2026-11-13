//! Persistent memo for the linear-arithmetic proof search.
//!
//! Nearly all front-end time on a typical project is Fourier–Motzkin
//! elimination in `facts`: thousands of small systems, the same ones on every
//! build because most belong to unchanged library code. This cache remembers
//! the outcome of each system.
//!
//! Nothing here is trusted. A remembered proof is only the list of source
//! rows and multipliers; `facts` rebuilds the certificate from the current
//! system and re-verifies it before use, and searches again if that fails.
//! A remembered "no proof" can at worst reject a program, never accept one.
//!
//! The key is a 128-bit hash of the system with its terms renamed to their
//! rank in term order. The search depends only on that order and on row
//! order, so equal keys give the same search. Entries are tied to this exact
//! compiler binary, because a different solver may find different proofs.
use std::{
    collections::HashMap,
    fs,
    hash::{Hash, Hasher},
    io::Write,
    path::PathBuf,
    sync::{Mutex, OnceLock},
};

/// A remembered search result: `None` for "no proof", otherwise
/// `(denominator, [(source row, multiplier)])`.
pub(crate) type Outcome = Option<(i128, Vec<(u32, i128)>)>;

/// Start over rather than load an ever-growing file.
const MAX_FILE: u64 = 4 * 1024 * 1024;
/// One file per compiler binary; see [`prune`].
const MAX_FILES: usize = 32;

struct Store {
    entries: HashMap<u128, Outcome>,
    file: Option<fs::File>,
}

fn digest(bytes: &[u8], seed: u8) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    seed.hash(&mut hasher);
    bytes.hash(&mut hasher);
    hasher.finish()
}

/// The key of a serialized system.
pub(crate) fn key(bytes: &[u8]) -> u128 {
    (u128::from(digest(bytes, 1)) << 64) | u128::from(digest(bytes, 2))
}

fn directory() -> Option<PathBuf> {
    if std::env::var_os("KUSH_NO_PROOF_CACHE").is_some() {
        return None;
    }
    let root = if let Some(root) = std::env::var_os("KUSH_PROOF_CACHE") {
        PathBuf::from(root)
    } else if let Some(root) = std::env::var_os("XDG_CACHE_HOME") {
        PathBuf::from(root).join("kush/proofs-v1")
    } else {
        PathBuf::from(std::env::var_os("HOME")?).join(".cache/kush/proofs-v1")
    };
    // Same policy as the runtime cache: private, owned by this user, and
    // never reached through a symlink. Otherwise simply do not cache.
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
        if metadata.mode() & 0o077 != 0 || metadata.uid() != fs::metadata("/proc/self").ok()?.uid()
        {
            return None;
        }
    }
    Some(root)
}

/// One file per compiler binary.
fn path() -> Option<PathBuf> {
    let executable = fs::canonicalize(std::env::current_exe().ok()?).ok()?;
    let metadata = fs::metadata(&executable).ok()?;
    let identity = format!(
        "{executable:?}:{:?}:{}",
        metadata.modified().ok()?,
        metadata.len()
    );
    Some(directory()?.join(format!("{:016x}.proofs", digest(identity.as_bytes(), 0))))
}

fn encode(key: u128, outcome: &Outcome) -> Vec<u8> {
    let mut payload = Vec::new();
    match outcome {
        None => payload.push(0),
        Some((denominator, weights)) => {
            payload.push(1);
            payload.extend_from_slice(&denominator.to_le_bytes());
            for (row, multiplier) in weights {
                payload.extend_from_slice(&row.to_le_bytes());
                payload.extend_from_slice(&multiplier.to_le_bytes());
            }
        }
    }
    let mut record = Vec::with_capacity(payload.len() + 28);
    record.extend_from_slice(&key.to_le_bytes());
    record.extend_from_slice(&(payload.len() as u32).to_le_bytes());
    record.extend_from_slice(&payload);
    let checksum = digest(&record, 3);
    record.extend_from_slice(&checksum.to_le_bytes());
    record
}

/// Read records until the first one that is truncated or damaged. Returns
/// the entries (a later record for a key replaces an earlier one) and the
/// length of the intact prefix.
fn decode(all: &[u8]) -> (HashMap<u128, Outcome>, usize) {
    let mut bytes = all;
    let mut entries = HashMap::new();
    while let Some((header, rest)) = bytes.split_at_checked(20) {
        let key = u128::from_le_bytes(header[..16].try_into().unwrap());
        let length = u32::from_le_bytes(header[16..].try_into().unwrap()) as usize;
        let Some((payload, rest)) = rest.split_at_checked(length) else {
            break;
        };
        let Some((checksum, rest)) = rest.split_at_checked(8) else {
            break;
        };
        if checksum != digest(&bytes[..20 + length], 3).to_le_bytes() {
            break;
        }
        let outcome = match payload.split_first() {
            Some((0, [])) => None,
            Some((1, body)) if body.len() >= 16 && (body.len() - 16) % 20 == 0 => {
                let denominator = i128::from_le_bytes(body[..16].try_into().unwrap());
                let weights = body[16..]
                    .as_chunks::<20>()
                    .0
                    .iter()
                    .map(|chunk| {
                        (
                            u32::from_le_bytes(chunk[..4].try_into().unwrap()),
                            i128::from_le_bytes(chunk[4..].try_into().unwrap()),
                        )
                    })
                    .collect();
                Some((denominator, weights))
            }
            _ => break,
        };
        entries.insert(key, outcome);
        bytes = rest;
    }
    (entries, all.len() - bytes.len())
}

/// Every rebuilt compiler starts a new file. Before adding one, keep only
/// the most recently used files so the directory stays bounded.
fn prune(new: &std::path::Path) {
    let Some(directory) = new.parent() else {
        return;
    };
    let Ok(entries) = fs::read_dir(directory) else {
        return;
    };
    let mut files: Vec<(std::time::SystemTime, PathBuf)> = entries
        .filter_map(|entry| {
            let entry = entry.ok()?;
            let path = entry.path();
            let metadata = fs::symlink_metadata(&path).ok()?;
            (metadata.is_file() && path.extension().is_some_and(|e| e == "proofs"))
                .then_some((metadata.modified().ok()?, path))
        })
        .collect();
    files.sort();
    let excess = (files.len() + 1).saturating_sub(MAX_FILES);
    for (_, path) in files.into_iter().take(excess) {
        let _ = fs::remove_file(path);
    }
}

fn store() -> &'static Mutex<Store> {
    static STORE: OnceLock<Mutex<Store>> = OnceLock::new();
    STORE.get_or_init(|| {
        let mut entries = HashMap::new();
        let file = path().and_then(|path| {
            // Only ever a regular file of ours, never something planted.
            match fs::symlink_metadata(&path) {
                Ok(metadata) if !metadata.is_file() => return None,
                Ok(metadata) if metadata.len() > MAX_FILE => {
                    let _ = fs::remove_file(&path);
                }
                _ => {}
            }
            let mut intact = None;
            if let Ok(bytes) = fs::read(&path) {
                let (read, length) = decode(&bytes);
                entries = read;
                if length < bytes.len() {
                    intact = Some(length as u64);
                }
            } else {
                prune(&path);
            }
            let mut options = fs::OpenOptions::new();
            options.append(true).create(true);
            #[cfg(unix)]
            {
                use std::os::unix::fs::OpenOptionsExt;
                options.mode(0o600);
            }
            let file = options.open(path).ok()?;
            // Records after a damaged one would never be read again, so cut
            // the file back to its intact prefix before appending.
            if let Some(length) = intact {
                let _ = file.set_len(length);
            }
            // `prune` keeps the most recently used files.
            let _ = file.set_modified(std::time::SystemTime::now());
            Some(file)
        });
        Mutex::new(Store { entries, file })
    })
}

pub(crate) fn get(key: u128) -> Option<Outcome> {
    store().lock().ok()?.entries.get(&key).cloned()
}

/// Remember an outcome in this process and, best effort, on disk. Each record
/// is one append, so concurrent compilers interleave whole records.
pub(crate) fn put(key: u128, outcome: Outcome) {
    let Ok(mut store) = store().lock() else {
        return;
    };
    let record = encode(key, &outcome);
    // A changed outcome is appended too: it replaces a stored entry that
    // failed verification, and the last record for a key wins on reading.
    if store.entries.insert(key, outcome.clone()) != Some(outcome)
        && let Some(file) = &mut store.file
    {
        let _ = file.write_all(&record);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn records_round_trip_and_damage_stops_the_read() {
        let proof: Outcome = Some((6, vec![(0, 3), (7, i128::MAX)]));
        let mut bytes = encode(1, &None);
        bytes.extend(encode(u128::MAX, &proof));
        let (entries, length) = decode(&bytes);
        assert_eq!(length, bytes.len());
        assert_eq!(entries.len(), 2);
        assert_eq!(entries[&1], None);
        assert_eq!(entries[&u128::MAX], proof);
        // A flipped byte in the second record keeps only the first.
        let last = bytes.len() - 12;
        bytes[last] ^= 1;
        let first = encode(1, &None).len();
        assert_eq!(decode(&bytes), (HashMap::from([(1, None)]), first));
        // A truncated tail is ignored, and the intact prefix is reported so
        // the file can be cut back to it.
        assert_eq!(decode(&bytes[..bytes.len() - 30]).1, first);
        assert_eq!(decode(&[1, 2, 3]), (HashMap::new(), 0));
        // The last record for a key wins.
        let mut replaced = encode(7, &None);
        replaced.extend(encode(7, &proof));
        assert_eq!(decode(&replaced).0[&7], proof);
    }
}
