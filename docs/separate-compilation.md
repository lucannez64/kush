# Separate compilation and shared libraries (design)

Status: design, not implemented. Tracked by `SEPCOMP-*` in `plan/plan.json`.

## Goal

Build times like C's: a program's build should cost in proportion to the
program's own code, not to its dependencies. Dependencies are compiled once,
installed as shared libraries, and linked, not rebuilt or bundled into every
program (the Gentoo model).

Today every dependency is a source package (`Kush.toml` path
dependencies). Each `kush build` loads the whole package graph as one
program, checks all of it, and compiles it into one executable. There is no
separate compilation, build cache or prebuilt library. On the generated
programs in `benchmarks/build-scale`, a development build is already faster
than a `rustc` debug build, but that cost is paid for every dependency on
every build, and an LLVM release build re-optimizes all of them.

## Decisions

These were settled on 2026-11-12:

| Question | Decision |
| --- | --- |
| What a package builds to | A shared library (`.so`), dynamically linked and installed once system-wide or under a prefix. |
| Generic functions across a library boundary | Specialized in the user. The library's interface carries the generic body; each program compiles the specializations it uses, as C++ templates and Rust do. |
| Interface changes | Each interface carries a hash of everything a client compiles against. A mismatch is refused at build time and at load time, and dependents are rebuilt (Gentoo sub-slots). No stable-ABI rules. |
| `dyn Trait` across libraries | Vtables: one table of function pointers per (type, trait), as in C++ and Rust, replacing the closed-world member table where a trait's implementations can span libraries. |

## Design

### Library build

`kush build --lib` compiles a package into:

- `lib<name>.so`, holding the compiled non-generic functions, drop glue,
  vtables and data;
- `<name>.kushi`, the interface. It holds every public item a client needs
  to check and compile against the library: type and layout definitions,
  function signatures with their effects, grades, lifetimes, contracts and
  propositions, trait and impl declarations, and the checked bodies of
  generic and `#[inline]` functions. It also holds the ABI hash (below) and
  the hashes of the interfaces it was built against.

The interface is generated, never written by hand, and is checked when it
is read: a client never trusts a body or a fact it has not verified.

### Program build

A dependency may name an installed library instead of a source path:

```toml
[dependencies]
words = { version = "0.1" }          # an installed library
local = { path = "deps/local" }      # a source package, as today
```

Installed libraries are found on a search path (`KUSH_LIBRARY_PATH`, then
`<prefix>/lib/kush`), laid out as `<name>-<version>/{lib<name>.so,<name>.kushi}`.
Building a program reads the interfaces of its dependencies, checks and
compiles only its own modules and the generic specializations it uses, and
links each dependency's `.so` with an `RPATH`/`RUNPATH` per the usual distro
conventions. `Kush.lock` records each library's version and ABI hash.

### The runtime as a shared library

The C runtime (allocator and pool, live-allocation accounting, task
scheduler, effect-handler stack, stack guard) is compiled privately into each
executable today, with internal symbols. With several Kush libraries in one
process there must be exactly one of each, so the runtime becomes
`libkushrt.so`, versioned and ABI-hashed like any other library. The LLVM
backend's inlining of small runtime functions remains possible for functions
that touch no shared state.

### ABI hash

The hash covers everything a client's compiled code depends on: layouts and
field offsets, enum tags and niches, function symbols and calling
conventions (including erased `@[0]` parameters), effect and handler
representations, vtable layouts, the bodies of exported generic and inline
functions, the runtime's ABI hash, and the compiler's codegen version. It does
not cover private items. A library change that keeps the hash needs no
rebuild of dependents; any other change is refused until they are rebuilt.

### Generics

A client specializes an exported generic function from the body in the
interface, under a symbol unique to the specialization. Two libraries that
specialize the same function at the same types get equal code; the duplicate
symbols are made local to each library (or weak), so nothing is shared by
accident across library versions.

### `dyn Trait`

A trait whose object type is used across a library boundary dispatches
through a vtable per (type, trait): method pointers, drop glue, size and
alignment. The closed-world union (and the whole-program agreement on
associated types it relies on) stays available within one library or
program, where it is faster; the compiler picks it only when the member set
is known to be complete.

### What a library boundary costs at run time

The same as in C: calls across it are not inlined, and the LLVM backend's
loop optimizations (deferred overflow checks, hoisted bounds checks) apply
inside each library but not across a call into it. Link-time optimization
across Kush libraries can come later as an opt-in for release builds.

### Within one package

The same machinery, per module: each module is checked against the
interfaces of the modules it imports, compiled to its own object, cached by
content hash, and rebuilt only when it or an interface it uses changes.
Independent modules compile in parallel, which also addresses the LLVM
release build time measured in `benchmarks/build-scale` (one module, one
core today).

## Open questions

- What the checker's proof cache and propositions need from an interface for
  a client to reuse a library's facts without re-proving them.
- Whether effect handlers and tasks need anything beyond the shared runtime
  across a boundary (handler frames installed by one library and performed
  in another).
- Versioned symbol names (`words_0_1_…`) or ELF symbol versioning.
- How `kush test` and the language server find installed libraries.

## Order of work

1. Interface files: emit and read them for a source package, and check a
   program against them, still compiling everything (no behaviour change).
2. The runtime as `libkushrt.so`.
3. `kush build --lib` and programs linked against installed libraries,
   non-generic exports first, then generic ones.
4. The ABI hash, enforced at build and load time.
5. Vtables for `dyn Trait` across libraries.
6. Per-module compilation and caching within a package, in parallel.

Each step is measured on a version of `benchmarks/build-scale` split into a
program and several dependency libraries, against `rustc` and against `cc`
on a C version of the same program.
