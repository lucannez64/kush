# Crypto building blocks: hashes, HMAC, Base64, random bytes

Status: implemented (WEB-CRYPTO), for the web framework
([web.md](web.md)): signed session cookies, CSRF tokens, the WebSocket
handshake. All of it is ordinary Kush in std except the random source, which
is one `kush_sys_*` host call. Tests: `crates/kush/tests/std_crypto.rs`
(known-answer vectors on both backends, balanced allocations).

```kush
use std.sha256;
use std.hmac;
use std.base64;
use std.random;

let digest = sha256.digest(&data);                    // 32 bytes
let tag = hmac.sign(&key, &message);                  // HMAC-SHA256
if hmac.verify(&key, &message, &received) { .. }      // constant time
let cookie = base64.encode_url(&tag);                 // no padding
let token = random.bytes(32)?;                        // from the kernel
```

| Module | Functions | Notes |
| --- | --- | --- |
| [`std.sha256`](../crates/kush/std/sha256.kush) | `digest`, `new`, `update`, `finish` | FIPS 180-4. `update` consumes and returns the `Hasher`. |
| [`std.sha1`](../crates/kush/std/sha1.kush) | same | Broken for collisions; only for protocols that require it (RFC 6455). |
| [`std.hmac`](../crates/kush/std/hmac.kush) | `sign`, `verify` | HMAC-SHA256 (RFC 2104). Keys over 64 bytes are hashed first. |
| [`std.ct`](../crates/kush/std/ct.kush) | `equal` | Comparison whose time depends only on the lengths. |
| [`std.base64`](../crates/kush/std/base64.kush) | `encode`, `encode_url`, `decode`, `decode_url` | RFC 4648; decoding returns `Option<Bytes>`. |
| [`std.random`](../crates/kush/std/random.kush) | `bytes` | `getrandom(2)`; `Result<Bytes, i64>` with errno. |

## Choices

- **Wrapping arithmetic is explicit.** Kush integers are checked, so SHA
  additions use `Int.wrapping_add` and rotations shift a `u64` copy of the
  word: no checked shift ever drops a bit, and no overflow check is turned
  off.
- **Canonical Base64.** Decoding rejects characters outside the alphabet,
  missing or misplaced `=` (standard form), any `=` (URL form), an
  impossible length, and nonzero unused bits in the last character. Each
  byte string has exactly one accepted encoding, so decoded tokens can be
  compared or used as keys.
- **`hmac.sign`, not `hmac.sha256`.** The module imports `std.sha256`, and a
  function of the same name would shadow it. HMAC here is always SHA-256.
- **Random bytes only from the kernel.** There is no seeded generator in
  std; anything security-related must come from `random.bytes`. The native
  stub retries short reads and `EINTR`; the reference evaluator reads
  `/dev/urandom`. Like `kush_sys_read`, the call fills the buffer's spare
  capacity and frees the buffer on failure.

## Limits

- **Constant time is best effort.** `ct.equal` has no early exit and no
  branch on the data, but neither Cranelift nor LLVM is told to keep it that
  way; this is the usual guarantee of portable code, not a statement about
  the machine code.
- **Speed.** The hashes allocate a message schedule per 64-byte block and
  read bytes with checked `Bytes.get`; a million bytes hash in well under a
  second natively. Proved reads (`Bytes.at`) and a reused schedule are the
  obvious next steps if hashing shows up in a profile.
- **No AES, no signatures, no key exchange.** TLS is handled by rustls
  through `kush bindgen` (WEB-TLS), not by Kush code.
