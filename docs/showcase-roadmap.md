# Showcase roadmap

Status: chosen by the user 2026-11-13, after the Game Boy emulator
([examples/gameboy](../examples/gameboy/README.md)). Each project gives one
sentence and one artifact a stranger can share, and each forces a feature
into the language. Plan nodes are named in brackets; dependencies are in
`plan/plan.json`.

Successful languages tend to be promoted by one serious product (Go and
Docker, Zig and Bun), by self-hosting (Lean's compiler and Lean4Lean), by a
landmark result (Lean and FLT, F\* and HACL\*), by one reproducible number, or
by a short live demo. The tracks below cover those patterns.

## Quick wins on features that exist

**Proof report to fuzz targets** [PROOF-FUZZ]. *Every check is either proved
or attacked.* `KUSH_PROOF_REPORT` lists the bounds and overflow checks the
prover could not discharge. Generate a fuzzer aimed at exactly those spots;
a counterexample becomes a bug report or a lemma to prove.

**Privacy budgets as grades** [DP-GRADES]. *Over-spending the privacy budget
does not compile.* A grade algebra for sensitivity and epsilon, as in the
research languages Fuzz and Duet, inside a systems language; a small
privacy-preserving metrics library as the example.

**Semver checked by the compiler** [SEMVER-CONTRACTS, SEMVER-ENSURES]. *A minor
upgrade that breaks you is impossible.* v1 extracts a package's public
contracts (types, effect rows, grades) and requires the new version's
signatures to be subtypes of the old ones, reusing the effect- and grade-aware
arrow subtyping; `kush semver` and `Kush.lock` resolution enforce it. v2 adds
preconditions (weaker) and `ensures` (stronger), checked by the prover, with
the failed implication as the explanation.

## Staging track: the viral demo

**Staging** [STAGING-DESIGN, STAGING, STAGING-RUNTIME]. *An interpreter that
becomes a compiler.* Typed quotes and splices (`Code<T>`, as in MetaOCaml),
checked before the generated code runs, with hygiene; then running staged code
at run time through the native backend.

**Staged Game Boy** [GB-STAGED]. Specialize the emulator's interpreter loop
against a ROM: the first Futamura projection, on a real program.

**Game Boy JIT** [GB-JIT]. SM83 blocks compiled to x86-64 at run time, from
about 65 times the console's speed towards 1000. Executable memory is a linear
resource: writable or executable, never both. The demo: the same game, flip to
the staged build, watch the frame counter.

**Write-once formats** [FORMATS-ROUNDTRIP]. *Write the format once; never write
a parser again.* One description of a binary format (save states, kush-kv
records, protocol messages); staging generates the parser and the serializer
and the prover shows `parse(serialize(x)) == x`.

## Kernel track: credibility

**Kernel in Kush** [KERNEL-IN-KUSH]. *Kush checks its own kernel.* Port the
logical kernel (universes, `J`, indexed data, `Prop`) to Kush, as Lean4Lean
does for Lean, with its invariants (substitution preserves well-scopedness)
checked by the Rust kernel.

**A prover built on effect handlers** [TACTICS-HANDLERS]. Tactics are effects
(`perform Goal`, `perform Choose`, `perform Fail`); backtracking search is a
multishot handler; proof scripts are ordinary Kush programs whose terms the
Kush kernel checks.

## Where the tracks meet: real software

**Session types** [SESSION-TYPES, SESSION-NET]. *Breaking the protocol does not
compile.* Protocols as linear channel types (`Chan<Send<Move, Recv<State,
..>>>`), first between threads and tasks, then over TCP with write-once formats
as the wire layer; multiparty protocols with dependent payloads later.

## Later

- Full self-hosting [SELF-HOST]: parser, checker and backend in Kush.
- A hardware backend (staged Kush to Verilog, the SM83 on an FPGA), once
  there is a board to test on.
