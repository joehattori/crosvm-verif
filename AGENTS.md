# Agent instructions

Read [README.md](README.md) for project context and build commands. See
[Resources/README.md](Resources/README.md) for the verified scope and model
assumptions. Keep those descriptions in their respective READMEs rather than
duplicating them here.

# Repository map

| Path | Role |
| --- | --- |
| [crosvm/](crosvm/) | Pinned upstream Rust submodule; the current sources of interest are [address_range.rs](crosvm/resources/src/address_range.rs) and [address_allocator.rs](crosvm/resources/src/address_allocator.rs). |
| [aeneas/](aeneas/) | Pinned toolchain submodule, including the [Lean library](aeneas/backends/lean/) and [examples](aeneas/tests/lean/). |
| [Resources/Types.lean](Resources/Types.lean), [Resources/Funs.lean](Resources/Funs.lean) | Generated types and functions. |
| [Resources/TypesExternal_Template.lean](Resources/TypesExternal_Template.lean), [Resources/FunsExternal_Template.lean](Resources/FunsExternal_Template.lean) | Generated declarations for missing external models. |
| [Resources/TypesExternal.lean](Resources/TypesExternal.lean), [Resources/FunsExternal.lean](Resources/FunsExternal.lean) | Handwritten external type and function models. |
| [Resources/AddressRangeSpec.lean](Resources/AddressRangeSpec.lean) | Mathematical predicates and proofs for address ranges. |
| [Resources/AddressAllocatorSpec.lean](Resources/AddressAllocatorSpec.lean) | Allocator constructor initialization proofs. |
| [Resources/README.md](Resources/README.md) | Detailed verification scope, model assumptions, and extraction notes. |
| [Resources.lean](Resources.lean) | Library entry point checked by the default build. |

# Editing rules

- Keep generated Lean reproducible. Change Rust, extraction configuration, or
  the translator as appropriate, then regenerate; do not hand-edit generated
  definitions to make a proof succeed.
- Keep proofs in handwritten specification modules. Maintain external models
  in `FunsExternal.lean`; do not overwrite it with the generated template.
  After extraction, reconcile any changed template signatures and inspect the
  generated diff before updating proofs.
- Import new specification modules in `Resources.lean` so the default build
  checks them.
- Use the pinned Lean dependencies; avoid incidental dependency upgrades.
  Use the Makefile's extraction flags rather than a separate invocation.
- Treat both submodules as pinned dependencies. Modify their contents or
  revisions only when needed for the requested task, and report those changes.
  For work inside crosvm, consult `crosvm/.agents/AGENTS.md` and its contribution
  workflow. For Aeneas changes, consult `aeneas/CLAUDE.md` and relevant local docs.

# Proof standards

- Keep claims tied to the functions, assumptions, and properties actually
  verified.
- Read the Rust implementation and its generated Lean before stating a theorem.
  Prove a meaningful mathematical property of the translated function, with
  explicit preconditions where needed. Do not weaken a requested property or
  assume its conclusion merely to finish a proof. Report counterexamples or
  translation limitations when they prevent the intended result.
- Follow the existing `f args ⦃ result => property ⦄` specifications and register
  reusable function specifications with `@[step]` where appropriate. Prefer
  composing proved specifications with `step`, then use `simp`, `simp_all`,
  `scalar_tac`, or `omega` for the remaining obligations. Search the local Aeneas
  library and existing proofs before adding duplicate helper lemmas.
- Respect bounded Rust arithmetic. Use `U64.val` and `U64.max` to express
  mathematical bounds, and discharge overflow and underflow obligations.
  Distinguish an expected `Option.none` return from failure in Aeneas's `Result`.
- Preserve the source semantics of inclusive address ranges: emptiness is
  `end < start`, and any such pair represents an empty range. Rust equality
  considers all empty ranges equal; Lean structure equality compares fields.
  Account for zero sizes, empty ranges, endpoints, and `u64::MAX` where relevant.
- Do not leave `sorry`, `admit`, or new axioms as completed proofs, or use
  `native_decide` to bypass kernel-checked proof construction. A successful build
  alone does not establish that a theorem is free of proof holes or assumptions.
- External models are part of the trust boundary: match their Rust semantics
  and make assumptions explicit. Do not treat existing axioms or generated
  placeholders as proved behavior. Use `#print axioms theoremName` when auditing
  theorem dependencies.

# Validation and reporting

After changing Lean proofs or models, run the verification command in the
[build and extraction guide](README.md#build-and-extraction) and inspect warnings
as well as errors. After changing extraction inputs, regenerate first and then
verify. If Rust code changes, also run the relevant crosvm checks according to its
contribution workflow. Documentation-only changes need path and command
consistency checks, not a toolchain rebuild.

Report the properties proved, files changed, commands run and their outcomes,
and any remaining assumptions or unverified steps. Distinguish checking the
committed Lean translation from validating a freshly regenerated translation.

# Local references

- [Getting started with Aeneas](aeneas/documentation/getting-started.md)
- [Proof strategies](aeneas/documentation/proof-strategies.md)
- [Tactics reference](aeneas/documentation/tactics-reference.md)
- [Tips and tricks](aeneas/documentation/tips-and-tricks.md)
- [Lean tutorial examples](aeneas/tests/lean/Tutorial/)
