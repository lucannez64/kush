# Lifetime variance implementation status

Status: LT-VAR-TABLE, LT-VAR-CONTEXT, LT-VAR-CHECK and LT-VAR-TESTS are
implemented for the fragment below. `LT-VARIANCE` remains the integration gate
for the full compiler path in
[lifetime variance design](lifetime-variance-design.md).

This is a lifetime-only judgment. It does not add runtime type-argument
subtyping, representation changes, higher-rank syntax, or new layout rules. A
variance result is checker-only evidence; both backends emit the same values
and layouts as before.

## Implemented

- `crates/kush/src/variance.rs` contains the four-element sign-set lattice
  (`unused`, `positive`, `negative`, `invariant`), join and composition with
  the unused/invariant rule, direct-occurrence seeds, and a bounded
  deterministic worklist fixed point over declaration lifetime slots. A
  declaration's self edge never creates variance by itself; a `value` field or
  another seeded occurrence must supply it.
- `Types` builds the finite table from record and alias declarations and caches
  it by declaration and lifetime slot. `Box`/`Vec` borrowed payloads compose
  positively, shared references and slices positively, `&mut` pointees and
  mutable container elements invariantly, and a structural row's erased outer
  field borrow positively (a row declares no lifetime parameters of its own;
  retained borrowed fields remain exact under an actual structural
  conversion).
  Arena/custom-allocator storage, `TaskExit`, optional-reference enums, foreign
  resources, trait objects and unknown generic arguments stay exact or
  invariant rather than acquiring covariance.
- `LabelEnv` classifies labels at one checked occurrence as free (rigid),
  bound (alpha-renamable), or internal (rigid). It is not stored on an interned
  function-type ID. Callable conversion builds its environment per occurrence.
- `borrow_witness` compares two callable contracts position by position and
  returns a path/polarity witness. It preserves the existing parameter
  contravariance, result covariance, many-source-to-one-target instantiation,
  bound implication and result-flow rules. `BorrowSig::usable_as` now consumes
  this witness.
- `witness` walks two erased-shape-compatible type occurrences and checks each
  borrowed leaf: positive requires source outlives target, negative requires
  the reverse, invariant requires identical binder identity. Unclassified or
  missing labels are unresolved, never erased acceptance.
- `runtime_types::BorrowLeaf` carries the signed occurrence direction. The
  ownership pass uses it for nested record/container construction, returned
  borrowed records, and mutable container writes. This keeps destination
  declared labels authoritative and preserves the existing owner-loan rules.
- Same-scope conversions in the executable checker run the contextual witness
  for every borrowed conversion, including call results and coerced values.
  Direct, indirect, and statically dispatched method calls collect each
  declared callee binder occurrence across every argument. Invariant
  occurrences must agree on one actual lifetime identity; covariant and
  contravariant occurrences may use a different actual lifetime only when an
  established caller outlives edge proves the required direction, and declared
  callee bounds are checked after instantiation. Resolution is per call, not a
  blanket same-label rule. Record literal inference uses only fields whose
  declared type mentions the lifetime, so an unrelated field cannot supply or
  poison the identity.
- A fresh argument placeholder is not compared as a caller identity; the call
  occurrence constraints own that relation. In contrast, a nested block, `if`,
  `match`, or immediately called lambda used as an argument keeps its normal
  same-scope obligations. An unresolved callee binder with no parameter
  occurrence becomes a distinct opaque identity rather than keeping its raw
  printed name, so a caller binder with the same name cannot masquerade as the
  callee identity.

## Tests

- Exhaustive algebra, composition/join distributivity, seedless recursive
  graphs, order independence, and unused/invariant units in
  `variance::tests`.
- `crates/kush/tests/lifetime_variance.rs` covers by-value shortening and
  extension failure, invariant mutable pointee identity, callable direction and
  alpha/many-to-one conversion, two occurrences sharing one interned arrow,
  anonymous intersections and elision, owner retention after shortening,
  destination-declared mutable writes, structural result-field covariance with
  exact structural conversions, and structural/TaskExit conservatism.
- Existing `lifetimes`, `borrowed_records`, `borrowing_references`,
  `borrowing_extensions`, `subtyping`, `functions`, `generic_traits`, `traits`
  and `advanced_types_effects` suites remain green locally.

## Remaining limitations

- The table summaries record and alias lifetime parameters. Runtime enums have
  no lifetime parameters, so a lifetime nested in an enum type argument is
  treated conservatively; optional-reference enums remain invariant until an
  explicit payload-to-label mapping exists.
- Structural rows keep retained borrowed leaves exact; their row-specific
  provenance contract is separate work.
- `TaskExit<T>`, capture-result callables, trait objects, foreign resources and
  custom-allocator storage keep their existing exact contracts.
- `borrow_leaves` does not enumerate nested borrowed records reached through an
  owner reference (`&Record`/`&mut Record`). Invariant positions behind
  `&mut Box<...>` or `&mut Vec<...>` are enforced by the contextual witness for
  fully labelled same-scope conversions and by the mutable-container write
  checks; a dynamic leaf check for a borrowed record stored behind an owner
  reference remains future work.
- Elided and internal labels are never converted into a named lifetime. An
  invariant conversion involving an internal/fresh identity or an unclassified
  label is rejected without an identity proof; a non-invariant occurrence may
  still defer to the existing call/provenance evidence rather than inventing a
  relation.
- Call constraints see lifetime labels carried by record slots and container
  elements. An outer reference or slice label with no record occurrence remains
  represented by the ownership provenance pass rather than a named type label,
  so that established contract is preserved; indirect calls currently check
  record/container occurrences but do not re-check canonical arrow bounds.
- Dynamic `dyn` dispatch and compiler builtins keep their existing contracts and
  are not broadened by these call constraints.
- No new higher-rank callable inference is added. Canonical arrow labels are
  still mapped by the established positional instantiation rule.
