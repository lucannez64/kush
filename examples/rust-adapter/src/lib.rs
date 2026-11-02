//! Rust library exposed to Kush through generated checked adapter shims.
//!
//! `ffi.rs` and `src/sha256_adapter.kush` are generated from `Bridge.toml` by
//! `kush bindgen` (which uses `kush::interop::AdapterSpec`). `bridge.rs` is the
//! ordinary safe Rust implementation, using the existing `sha2` crate. No
//! per-call raw FFI or foreign declaration is written by hand.
mod bridge;
mod ffi;

pub use bridge::*;
