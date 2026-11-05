# Representation-disjointness certificates for further unboxing

Status: **design** (RES-UNBOX-CERT). Nothing here changes a layout yet. It
defines the evidence the compiler must produce and check before it removes a
tag, so that today's niche encodings become *instances* of one checked rule
and any extension is justified by a certificate rather than by a case in
codegen. Implementation is split into the plan nodes at the end.

Input: [Unboxed data constructors, POPL 2024](https://doi.org/10.1145/3632893)
([manuscript](https://arxiv.org/abs/2311.07369)). It unboxes a single-argument
constructor when the *head shapes* of the argument's values are disjoint from
those of the other constructors, and bounds the expansion of nested type
definitions to guarantee termination. Kush borrows the two ideas (disjoint
value sets, bounded expansion); the OCaml value model (immediates vs tagged
blocks) does not apply to Kush's word layouts, so no result transfers.

## 1. Current contracts to preserve

From [niche layouts](niche-layouts.md) and [compact layouts](compact-layouts.md):

| Case | Encoding | Must stay |
| --- | --- | --- |
| two variants, one empty, payload `Box<T>` / `&T` / `&mut T` | empty = `0` | yes, bit for bit |
| ... payload `Bool` | empty = `2` | yes |
| ... payload `Char` | empty = `0x110000` | yes |
| other enums | explicit tag word | yes unless a certificate applies |
| nominal structs | no tag, fields in order | yes |
| `Result<T, E>`, tuples, structural rows, arrays, `DynArray`, foreign resources | existing ABI | yes (`Result` and foreign layouts are ABI contracts) |
| C bridge (`Bridge.toml`) | declared layouts | never touched by unboxing |

Drop glue, `Task.join`, `Slice.try_get`, `Char.from_code` and other builtin
producers share the layout decision and must keep doing so.

## 2. The question

What evidence shows that removing a tag (or merging alternatives into one
word) is unambiguous for every value, for every instantiation, and how far
may nested and recursive types be expanded while looking for that evidence?

## 3. Value-set domain

For every instantiated type `T`, define `V(T)`: for each physical word `i`,
the set of bit patterns a valid `T` value may hold in word `i`. Represent it as
a finite union of at most 8 closed intervals plus an alignment (`x ≡ 0 mod a`),
with `⊤` meaning "all 2^64 patterns".

| Type | `V` of its discriminating word |
| --- | --- |
| `i64`, `u64`, all fixed-width integers | `⊤` (no refinement types reach layout today) |
| `f64`, `f32` | `⊤`: **every NaN payload is a valid value**; Kush does not canonicalize NaNs, so floats never provide a niche |
| `Bool` | `{0, 1}` |
| `Char` | `[0, 0xD7FF] ∪ [0xE000, 0x10FFFF]` |
| `Box<T>`, `&T`, `&mut T` | `[1, 2^64-1]`, aligned to the allocator/stack alignment **once that contract is asserted** (section 6); until then only non-null is used |
| tagged enum with `n` variants | tag word `[0, n-1]` |
| niche-encoded enum | the union of its payload's set and its niche values |
| nominal struct | `V` of its first field (word 0) |
| function pointer, foreign resource, buffer/vector header | `⊤` (trusted host representations are not assumed non-null) |
| `Unit`-valued payload | a payload, not an empty variant (as today) |

`V` is computed structurally on instantiated types with memoization; a type
whose computation would re-enter itself without passing through an
indirection (`Box`, `Vec`, reference) is already an infinite-size error, and a
type that passes through an indirection stops there: the pointer's set does
not depend on its pointee. This is the **expansion bound**: expansion never
follows an indirection, and the nesting depth of inline enums examined for one
layout is capped at 4 (further nesting keeps its explicit tag).

## 4. Certificates

A layout choice for an enum `E` with variants `C₁ … Cₙ` that omits the tag
word comes with a certificate:

```text
Cert(E) = discriminating word w (always word 0 in this design),
          for each variant Cⱼ a set Sⱼ ⊆ 2^64 with
            Sⱼ = V(payload_j)(w)       for a variant with a payload, or
            Sⱼ = { kⱼ }               a chosen niche constant for an empty one
```

The **checker** (independent of the code that chose the layout) accepts the
certificate only if

1. **disjointness:** `Sᵢ ∩ Sⱼ = ∅` for all `i ≠ j` (interval arithmetic);
2. **soundness of each Sⱼ:** it is recomputed from `V`, not trusted from the
   chooser; a niche constant must lie outside every payload set;
3. **decodability:** the decoder emitted for matching, drops and builtin
   producers is the membership test of the certificate, generated from the
   checked certificate, so construction, matching and drop glue cannot drift;
4. **at most one payload variant whose set is not a singleton or a small
   interval list** (so the decoder stays a few comparisons);
5. the payload's other words are unaffected (only word 0 is shared).

Rejection means *explicit tag*, never a compile error. The reference
evaluator keeps its abstract tag; parity tests compare behaviour.

Today's three niche cases are exactly the certificates
`{Some: [1,2^64-1], None: {0}}`, `{Some: {0,1}, None: {2}}` and
`{Some: Char set, None: {0x110000}}`; the first implementation step must
re-derive them through the checker with **no** layout change.

## 5. Extensions the certificates enable (each needs its own node)

- **Several empty variants** (`enum E { A, B, Some(Bool) }` → `0,1` payload,
  `2`, `3` niches; `Char` has 0x110000-0xFFFFFFFF and the surrogate gap).
- **Nested propagation**: `Option<Option<Bool>>` → `{0,1}`, `2`, `3`; the
  inner enum's set includes its niche, and the outer picks a new constant
  outside it.
- **Tag-word niches**: a tagged enum's unused tag values (`[n, 2^64-1]`) can
  hold an outer enum's empty variants.
- **Pointer alignment niches** (`1..7` for 8-aligned boxes), only after the
  alignment contract is asserted in both runtimes (pool, headerless and
  system allocations, stack references).

Explicitly **not** proposed: float/NaN niches, integer niches without a
static range, unboxing through foreign resources or `Result`, multi-word
discrimination, and any layout whose decision depends on a generic parameter
before instantiation (layouts are per instantiation already).

## 6. Obligations and hostile tests

- Allocation alignment: a runtime test that every allocation path (pooled,
  headerless, system, arena, user allocator) returns a non-null pointer with
  the asserted alignment; references to stack locals likewise.
- Boundaries: `Char` 0xD7FF/0xE000/0x10FFFF and the surrogate gap; `Bool`
  produced by comparisons and by FFI (FFI `Bool` must be validated or the
  niche must not be used for foreign-produced values).
- NaNs with every payload pattern round-trip through enums unchanged.
- Owning payloads: drop exactly once for every variant under every encoding.
- Recursive types: `enum List { Nil, Cons(i64, Box<List>) }` keeps its
  current tagged encoding (two payload words), `enum Chain { End,
  Next(Box<Chain>) }` keeps its null niche, and expansion stops at `Box`; deeply nested inline enums beyond
  depth 4 keep tags.
- Union membership: an encoded enum inside a union keeps its own encoding and
  the union keeps its tag.
- Parity: evaluator and native (default and release) agree, allocations
  balanced.

## 7. Decisions

1. Unboxing is driven by **checked certificates** over a per-word value-set
   domain; the chooser is untrusted, the checker is small.
2. Discrimination uses **word 0 only**.
3. **Expansion never crosses an indirection** and inline nesting is capped at
   depth 4.
4. Floats and unrefined integers have **no niches**.
5. Existing encodings are reproduced bit for bit first; extensions come one
   per node with their own tests and a measured benefit.
6. Foreign layouts, `Result`, and the bridge ABI are out of scope.

## 8. Follow-up nodes

Added to `plan/plan.json`:

- **UNBOX-CERT-CHECKER** (M): value-set domain, certificate checker, and
  re-derivation of the three existing niche layouts through it with no
  layout change; decoders generated from certificates.
- **UNBOX-ALIGN-CONTRACT** (S): assert and test pointer alignment for every
  allocation path and stack references (section 6).
- **UNBOX-MULTI-NICHE** (M): several empty variants and nested propagation
  (section 5), with the hostile tests of section 6.
- **UNBOX-TAG-NICHE** (M): reuse unused tag values of inner tagged enums.
