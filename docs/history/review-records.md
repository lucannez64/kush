# Review records

Review narratives moved out of the design documents unchanged
(FND-DOC-HISTORY). The rules they led to stay in the design documents
and in [the reference](../reference/README.md); these sections record how
the reviews found them.

## From [borrowing-extensions.md](../borrowing-extensions.md)

### Review fixes and scope slice results

A slice returned from `Task.scope` retains the scope closure's capture-result
provenance. Its original storage remains borrowed through the returned view's
last use, and block-local storage cannot escape. Borrowed-record scope results
and borrowed `TaskExit` values across function boundaries keep the same
per-leaf provenance and are checked until their last use.

A borrowed `TaskExit<T>` cannot be hidden in a closure/task environment: match
it within the joining scope. Reading a stored reference for a field access is
a reborrow, while passing it as a call argument retains the child loan through
later argument evaluation. Multiple shared arguments are allowed; overlapping
exclusive arguments, including two uses of one stored `&mut`, are rejected.
These rules have dedicated native/reference and rejection regressions in
`tests/borrowing_safety.rs`.

## From [dynamic-arrays.md](../dynamic-arrays.md)

### Review

An independent review of the runtime-length array, pattern, slice-element
place, and field-view work found two soundness holes and five smaller issues.
All are fixed, and each has a regression test (`review_*` in
`crates/kush/tests/advanced_types_effects.rs`):

1. A write through a `&mut Record` parameter (`*h = ...`, `h.field = ...`)
   was accepted while a view, element reference, or borrowed-pattern binding
   derived from `h` was live, which could free a matched box. Such writes now
   wait for the derived borrow's last use.
2. A local whose address was taken by `&mut` kept its arithmetic facts (for
   example a loop counter's `0 <= i`), so `Slice.at` could read outside the
   slice. Such a local now leaves the fact system, and `&mut x` in a loop body
   counts as a write of unknown direction.
3. A borrowed match used directly as an outer arm's result was falsely
   rejected; its scrutinee loan now ends with the match.
4. A reference returned from one `split_at_mut` side conflicted with an
   element reference into the other side; call results now keep the side.
5. Diagnostics and limits: two length binders with one name are named apart in
   a mismatch, a literal argument for a runtime-length parameter gets the
   length-proof message, `[..rest]` alone is exhaustive, and `a[i]` works
   through `&mut [T; n <= C]`.

A second independent review covered the extensions (generic, method, trait,
and nested signatures, and exclusive patterns) over five rounds plus a
focused re-check, with local builds. It found seven soundness bugs, each
fixed with a regression test in `crates/kush/tests/runtime_length_extensions.rs`:

1. A recursive call whose type argument named the function's own length
   binder (`go::<[i64; n <= 4]>` inside `go`) gave a value of the outer
   length the inner activation's type. Such instances are rejected; the check
   also covers inherited trait defaults, whose per-impl copy has its own
   binding, and binders inside `dyn` trait arguments.
2. Rebinding a signature type at a call could change its layout: union
   members merged (`f(k, k, ...)` on `[i64; n <= 4] | [i64; m <= 4]`),
   swapped positions, absorbed a width subtype, or merged inside a generic
   record or enum. The rebuilt type must now be isomorphic to the callee's.
3. A type alias expanding to `dyn Tr<[i64; n <= 4]>` hid the binder from
   call-site substitution, so the callee's binder leaked into the caller's
   type. Binder walks now see `dyn` arguments, and such calls are rejected.

Smaller results: recursive calls forwarding their own binder were briefly
falsely rejected by an intermediate fix and are accepted again, and a guard
that writes through an exclusive binding does not change what later arms
test (documented).

## From [language-server.md](../language-server.md)

### Review corrections

The initial advertised extra-arguments setting was removed because the server
accepts only `kush lsp`. Open-document locations use the client's URI, and old
published diagnostics under another URI alias are cleared. Canonicalization of
existing parent directories keeps new unsaved paths stable when saved through
a symlinked workspace. Unsaved entry module headers receive package-name
validation even when the entry has later syntax errors, named-import navigation
selects the declaration name, and hover/document symbols/semantic tokens were
extracted from that same cursor probe.

## From [simd.md](../simd.md)

### Review fixes (SIMD-REVIEW, 2026-11-15)

An independent review (Codex) found two defects, both fixed:

- **A root file could stand in for std.** The loader registered the root's
  declared path before resolving imports, so a root named `module
  std.cpu;` was what the real `std.x86` imported: it could declare a public
  `Sha` and reach the SHA instructions with no CPUID check. A root named
  `std.x86` had its functions taken for the intrinsics. The loader now
  rejects a root under `std`, and the intrinsic table also skips the root
  unit. Test: `a_root_module_cannot_stand_in_for_std`.
- **The feature cache was a data race.** Two threads asking for a token
  first could read and write the cached bits at once; the accesses are now
  atomic.

The review found nothing else in lane order, endianness, signed
arithmetic, shift bounds, the 256-bit halves, shuffles, the LLVM vector
translation, the SHA round sequences, CPUID/XGETBV gating, or associated
functions and `Self`.

## From [recursive-lifetime-design.md](../recursive-lifetime-design.md)

### Independent review follow-up

An independent soundness review of the method, per-field and `R[f]` extension
found no accepted program that outlives an owner, aliases mutably, or reads
freed memory. It found four defects, fixed with regressions in
`tests/recursive_lifetimes.rs`:

- **Non-convergent unsupported relays.** A recursive call relaying a callee's
  unsupported channel wrapped its witness text again on every pass, so the
  fixed point never converged and source order changed the diagnostic. A
  relayed fact is now wrapped at most once and never preferred over a root
  cause (`Unsupported::relayed`).
- **Generic receivers.** A receiver typed by a generic binder or alias
  (`id(b).pick(..)`) matched an unrelated impl of the same name. Receiver
  names now count only when they resolve to a concrete data declaration;
  anything else is the explicit-contract boundary.
- **Whole-record identity helpers.** A callee returning a whole parameter
  merged every argument field owner into every result field, producing false
  cross-field bounds. The argument's per-field leaves now map to the same
  result fields.
- **Inherent methods and `R[f]`.** Inferred requirements are now exported for
  inherent methods. Trait impl, generic impl and default methods keep their
  exact contracts.

The branch-label check also now excuses only the slot whose own label is
compiler-internal, instead of every slot when any label was internal.

## From [postconditions.md](../postconditions.md)

### Soundness review (2026-11-06)

An adversarial review found false facts reaching code that ran; each is now
rejected and has a regression test (`review_regressions_for_postconditions`):

- a unit result returned implicitly (no tail, or an `if` without `else` in
  return position) is now a return point;
- a `Bool` goal is never weakened: an unknown part of `a && f(x)` makes the
  postcondition unstatable instead of dropping `f(x)`;
- a branch join drops the aliases of locals replaced on either path, and a
  loop drops the facts and aliases of every local it reassigns (not only
  scalars);
- any exclusive borrow (`&mut x`, `&mut x.field`, a `&mut self` method
  receiver, a mutable slice) makes its root local opaque to the facts, and a
  reference is never a value root, so writes through `&mut` cannot leave stale
  facts;
- a dropped hypothesis is skipped instead of being recorded as `false`;
- a foreign `Bool` result is normalised to 0 or 1 natively, matching the
  range the prover assumes;
- `IntOp::Unchecked` wraps like the machine operation in the evaluator too,
  so a wrong proof could never make the two backends disagree.
