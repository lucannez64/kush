use sha2::{Digest, Sha256};
use std::cell::RefCell;
use std::sync::atomic::{AtomicI64, Ordering};

static LIVE: AtomicI64 = AtomicI64::new(0);

/// Opaque owned Rust resource. Kush owns the handle and releases it exactly
/// once through the generated `kush_example_hasher_release` shim.
pub struct Hasher {
    inner: RefCell<Sha256>,
}

impl Hasher {
    fn new() -> Self {
        LIVE.fetch_add(1, Ordering::SeqCst);
        Self {
            inner: RefCell::new(Sha256::new()),
        }
    }
}

impl Drop for Hasher {
    fn drop(&mut self) {
        LIVE.fetch_sub(1, Ordering::SeqCst);
    }
}

fn hex(bytes: &[u8]) -> Vec<u8> {
    const DIGITS: &[u8; 16] = b"0123456789abcdef";
    let mut out = Vec::with_capacity(bytes.len() * 2);
    for byte in bytes {
        out.push(DIGITS[(byte >> 4) as usize]);
        out.push(DIGITS[(byte & 0x0f) as usize]);
    }
    out
}

pub fn add(a: i64, b: i64) -> i64 {
    a.wrapping_add(b)
}

pub fn sha256(data: &[u8]) -> Result<Vec<u8>, String> {
    let mut hasher = Sha256::new();
    hasher.update(data);
    Ok(hex(&hasher.finalize()))
}

pub fn hasher_new() -> Hasher {
    Hasher::new()
}

pub fn hasher_update(hasher: &Hasher, data: &[u8]) -> Result<i64, String> {
    hasher.inner.borrow_mut().update(data);
    Ok(i64::try_from(data.len()).map_err(|_| "input too large".to_owned())?)
}

pub fn hasher_finish(hasher: &Hasher) -> Result<Vec<u8>, String> {
    Ok(hex(&hasher.inner.borrow().clone().finalize()))
}

pub fn fail(_input: &[u8]) -> Result<i64, String> {
    Err("requested adapter failure".to_owned())
}

pub fn boom() -> Result<i64, String> {
    panic!("example adapter panic")
}

pub fn live() -> i64 {
    LIVE.load(Ordering::SeqCst)
}
