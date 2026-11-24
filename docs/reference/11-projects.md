# 11. Modules, projects and foreign code

## Modules

A file declares its module with `module a.b;` and imports others with
`use a.b;` (call through the last segment: `b.f()`) or `use a.b.Item;`
(call `Item` directly). Items and record fields are private to their module
unless marked `pub`; a record with a private field can only be built inside
its module.

```kush eval
use std.option.Option;
use std.option;

fn main() -> Unit ! {io, panic} {
    let some: Option<i64> = Option.Some(1);
    print_i64(option.unwrap_or(some, 0));
}
```

```output
1
```

Renamed imports (`use a.b as c`) do not exist yet (LANG-IMPORT-ALIAS).

## Projects

`kush new hello` creates a package:

```text
hello/
  Kush.toml
  src/main.kush        module hello;
  tests/main.kush      module hello.tests.main;
```

```toml
[package]
name = "hello"
version = "0.1.0"          # optional
entry = "src/main.kush"    # optional
test = "tests/main.kush"   # optional

[dependencies]
words = { path = "../words" }
```

`src/util.kush` is module `hello.util`, `src/parser/expr.kush` is
`hello.parser.expr`, and a dependency's `src/lib.kush` is its package name
(`use words;`). Dependencies are local paths only; `Kush.lock` pins the
resolved graph and `--locked` refuses to change it. Project commands:
`kush check`, `build`, `run [-- args]`, `test [FILTER]`, `fuzz`, `fmt
[--check]`, with `--manifest-path` to point at another project.

## Tests

`#[test]` functions take no parameters and return `Unit`; each runs in its
own process, and a panic fails it. `std.test` has assertion helpers.

```kush
use std.test;

#[test]
fn arithmetic() -> Unit ! {io, panic} {
    test.equal_i64(6 * 7, 42);
    test.is_true(1 < 2);
}

fn main() -> Unit ! {} { }
```

## Formatting and editor support

`kush fmt` normalizes whitespace and preserves comments and strings. `kush
lsp` is a language server with diagnostics, go-to-definition and formatting
([language-server.md](../language-server.md)).

## Foreign code

A foreign function is declared with its C symbol and no body; every foreign
call needs `io`. A host-owned resource is an empty record with a release
symbol; it is affine and released through that symbol.

```kush
#[foreign("example_hasher_release")]
struct Hasher {}

foreign "example_add" fn add(a: i64, b: i64) -> i64 ! {io};
foreign "example_new" fn new() -> Hasher ! {io};

fn main() -> Unit ! {} { }
```

Foreign signatures use scalars, `&Bytes`, `&mut Bytes`, owned `Bytes`,
resources and `Result<T, i64>`. Foreign code is trusted; the reference
evaluator rejects foreign calls. `[native]` in `Kush.toml` names the libraries
to link, and `kush bindgen Bridge.toml` generates Rust adapters and the Kush
declarations for safe Rust crates ([native-interop.md](../native-interop.md)).
`export "symbol" fn` exposes a Kush function to C, and `kush build --lib`
builds a static library with Rust bindings.
