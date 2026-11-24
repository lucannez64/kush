# Kush language reference

This is the language **as the compiler implements it today**. It replaces
[spec-v0.1.md](../spec-v0.1.md) as the description of what Kush is; the spec
remains the original design draft. Design documents in `docs/` keep the
rationale and history of each feature; this reference keeps only the rules.

Every Kush example in these chapters is checked against the compiler by
`scripts/check-reference.py`: plain blocks must check, `eval` blocks must run
and print the output shown, and `reject` blocks must fail with the diagnostic
quoted in them. When the compiler changes, the check fails until the reference
says the new truth. Limits are written as `reject` examples for that reason.

| Chapter | Contents |
| --- | --- |
| [1. Programs](01-programs.md) | files, `main`, printing, commands |
| [2. Syntax](02-syntax.md) | lexical rules, expressions, statements, control flow, patterns |
| [3. Types](03-types.md) | scalars, tuples, records, enums, arrays, text, collections, unions, aliases |
| [4. Functions](04-functions.md) | functions, generics, function values, lambdas and closures |
| [5. Traits](05-traits.md) | methods, traits, impls, associated items, trait objects |
| [6. Ownership and borrowing](06-ownership.md) | moves, copies, drops, linear values, borrows, slices, lifetimes |
| [7. Effects](07-effects.md) | effect rows, row polymorphism, panics, effect handlers |
| [8. Concurrency](08-concurrency.md) | structured tasks, threads, atomics, channels |
| [9. Proofs](09-proofs.md) | erased preconditions, `ensures`, invariants, the logical kernel |
| [10. Grades](10-grades.md) | usage grades as implemented today |
| [11. Projects](11-projects.md) | modules, packages, tests, formatting, foreign code |
| [12. Standard library](12-std.md) | the `std` modules |

## Changes under way

[foundations-review.md](../foundations-review.md) lists structural changes
that will change some rules below. Each chapter that is affected says so in a
"Planned changes" note naming the plan node. The decided ones:

- private functions will infer their effect rows (FND-ROWS-INFER); `panic`
  leaves effect rows (FND-ROWS-PANIC);
- one reference type `&'a T` with lifetimes in types replaces today's separate
  slice, text and record references (FND-REF-*);
- capturing closures that can be called more than once (FND-CLOSURE-*);
- stronger type inference (FND-INFER-*);
- lexical capabilities as the one handler model, and tasks as a library on
  handlers (FND-HANDLERS-ONE, FND-TASKS-ON-HANDLERS);
- proofs: the kernel behind the arithmetic facts (PROOF-*, FND-PROOF-TRUST);
- grades: graded modal types, after the rest (GRADE-*).

## Checking the reference

```sh
scripts/check-reference.py                 # every chapter, reference evaluator
scripts/check-reference.py --native        # also build and run eval blocks natively
scripts/check-reference.py docs/reference/03-types.md
```

The script uses `target/release/kush` (or `$KUSH`).
