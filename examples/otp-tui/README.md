# OTP TUI in Kush

A working recreation of `/home/hirew/Projects/otp-tui`: Kush owns the session's
interactive state, key handling, navigation, viewport, screen composition, and
CLI. A declarative Rust bridge reuses RustCrypto HMAC/SHA and crossterm rather
than recreating cryptographic primitives or a terminal backend.

## Build and run

From this directory, with a current `kush`, Cargo/Rust, and a C linker:

```sh
kush bindgen Bridge.toml --check
kush build
./target/kush/otp_tui
```

Or `kush run`. The project manifest builds the Rust static library and links it
with the Kush program. First build needs the dependencies in Cargo.lock from
crates.io; later builds reuse Cargo's adapter target cache. Native Linux x86-64
is the supported Kush target. Foreign calls do not run in `kush eval`.

For a quick demo using **public RFC test secrets**, never real accounts:

```sh
./target/kush/otp_tui --demo
```

The original project's source is untouched. This port is independently usable
as a Kush project inside the Kush repository.

## Interactive controls

| Key | Action |
| --- | --- |
| `a` | Add a TOTP or HOTP `otpauth://` URI; typed/pasted text is hidden |
| Enter / Escape | Add / cancel input |
| Backspace | Remove one Unicode scalar from input |
| `d` | Delete selected entry |
| `c` | Request clipboard copy of the selected code using terminal OSC 52 |
| `n` | Advance the selected HOTP counter explicitly |
| Up / Down | Previous / next entry |
| Page Up / Page Down | Jump ten entries |
| Home / End | First / last entry |
| `q` / Ctrl-C | Quit and restore terminal mode |

The screen updates every 100 ms, adjusts its viewport to terminal height, and
clips output by display width. For very small terminals, enlarge the window to
see the complete controls. OSC 52 clipboard support must be enabled in the
terminal; the app can report that it sent a request, not that a clipboard
manager accepted it.

## OTP compatibility

- TOTP and HOTP; SHA1, SHA256, SHA512.
- Six through ten decimal digits, custom positive TOTP period, full u64 HOTP
  counter (an exhausted counter cannot advance).
- Padded/unpadded, upper/lower-case Base32 secrets; percent-decoded UTF-8 labels.
- Invalid/duplicate/unknown URI parameters and mismatched issuer prefixes are
  rejected before insertion. Errors do not include the supplied URI or secret.
- Control characters cannot be injected into screen labels.
- At most 1000 session entries and 8192 bytes per input URI.

Unlike the original TUI, which accepts only TOTP entries even though its
library implements HOTP, this UI accepts both. HOTP does not advance merely
because a frame refreshes or a code is copied; press `n` deliberately.

## Headless codes

Read one URI from redirected stdin, not command-line arguments or shell history:

```sh
./target/kush/otp_tui --code-stdin < /path/to/protected-uri-file
```

For deterministic tests, add `--at SECONDS` (nonnegative Unix seconds):

```sh
printf '%s\n' 'otpauth://totp/RFC?secret=GEZDGNBVGY3TQOJQGEZDGNBVGY3TQOJQ&digits=8' |
  ./target/kush/otp_tui --code-stdin --at 59
# 94287082 — public RFC 6238 fixture
```

Headless mode reads until EOF, enforces the input bound, prints one code on
success, and returns a nonzero exit status for invalid input/options. Errors go
to stderr. Interactive mode requires a real terminal; `--help` and headless
mode work in pipelines.

## State and security boundary

Entries are **session-only**, matching the original application: no secret
files, automatic imports, encrypted vault, or persistence. HOTP counters also
reset when that session ends; this is not a persistent HOTP token replacement.
Closing the app discards the entries.

Decoded secrets in the Rust store use `Zeroizing<Vec<u8>>` and are erased on
removal/drop. This does **not** promise erasure of every copy: URI parsing,
Kush input/event buffers, HMAC internals, terminal/OS buffers, and allocations
may retain copies. The process does not use locked memory and is not a hardened
secret vault. The input prompt hides the URI; OTP codes remain visible and
clipboard contents are not automatically cleared.

Normal exits, Ctrl-C key handling, and returned errors release the opaque
terminal handle and restore raw mode/alternate screen. Forced termination,
SIGKILL, and process-aborting faults cannot guarantee restoration (`reset` or
`stty sane` can recover the shell). No terminal clipboard or other account data
is read.

The generated C ABI is a trusted Rust boundary, with checked Kush-side resource
ownership and errors. Generated code requires Rust `panic = "unwind"`.

## Layout and tests

- `main.kush`: CLI and startup.
- `src/ui.kush`: Kush event loop, navigation and frame composition.
- `Bridge.toml`: adapter contract; `src/adapter.kush` and `src/ffi.rs` generated.
- `src/bridge.rs`: opaque OTP storage, URI validation, RustCrypto, crossterm.
- `tests/main.kush`: generated-bridge, RFC, state and Kush UI tests.
- `scripts/smoke.py`: native CLI and real pseudo-terminal checks, public fixtures.

```sh
kush test
cargo test --manifest-path Cargo.toml --locked
python3 scripts/smoke.py
kush bindgen Bridge.toml --check
```

The Rust tests cover all ten RFC 4226 counters and all eighteen RFC 6238
SHA1/SHA256/SHA512 vectors, including large timestamps; parser failures,
period/digit bounds, counter overflow, label controls and UTF-8 backspace.
The PTY checks exercise real add/delete/copy/advance/navigation/resize and
verify terminal settings are restored after `q` and Ctrl-C. They inspect the
OSC 52 sequence, not the user's actual clipboard.

Specifications: [RFC 4226](https://www.rfc-editor.org/rfc/rfc4226) and
[RFC 6238](https://www.rfc-editor.org/rfc/rfc6238).

## Verified checkpoint

Validated locally and on Boat (Ubuntu 24.04, Rust 1.97.1, GCC 13.3.0):

- Five Rust test functions, including all 28 public HOTP/TOTP RFC vectors.
- Five Kush project tests, using the real generated native bridge.
- Rust formatting, Kush formatting, adapter Clippy with warnings denied, and
  generated-file drift checking.
- Native build, headless fixtures/errors, and real PTY add/delete/copy/HOTP/
  navigation/resize/hidden-input tests. Terminal flags are restored after both
  `q` and Ctrl-C. Ten repeated local Ctrl-C sequences also passed after the
  harness was synchronized to acknowledged resize frames.

Compiler sources were unchanged. These are application/adapter checks, not a
new run or an increased count of the compiler workspace's test suite. Boat
stopped with its build-cache snapshot preserved. Machine-local logs:
`/tmp/kush-boat-otp-tui-final.log` and
`/tmp/kush-boat-otp-tui-pty-final.log`.
