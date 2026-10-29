# Agent instructions

Read [README.md](README.md) for project context, the trust boundary, and build
commands. See [Resources/README.md](Resources/README.md) and
[VmMemory/README.md](VmMemory/README.md) for the verified scope. Keep those
descriptions in their respective READMEs rather than duplicating them here.

# Repository map

| Path | Role |
| --- | --- |
| [crosvm/](crosvm/) | Pinned upstream Rust submodule. The Makefile's `--start-from` and `--include` lines select the extracted items from the `resources`, `vm_memory`, and `base` crates. |
| [aeneas/](aeneas/) | Pinned toolchain submodule: our fork of Aeneas, which also pins and patches Charon. |
| [Resources/](Resources/), [VmMemory/](VmMemory/) | One directory per extracted crate. `Types.lean` and `Funs.lean` are generated; `*External_Template.lean` are generated declarations for missing external models; `TypesExternal.lean` and `FunsExternal.lean` are the handwritten models. `<Item>/Spec.lean` modules (plus helpers such as `AddressAllocator/Collections.lean`) hold the specifications and proofs. Each `README.md` gives the verified scope and its exceptions. |
| [Syscalls/](Syscalls/) | Trusted system call contracts and flag constants, e.g. `mmap(2)` and `munmap(2)` for the `MemoryMapping` proofs. |
| [Utils/](Utils/) | Code shared by both crates: alignment arithmetic, models of Rust core items (`CoreExternal.lean`), and the `Platform64` assumption. |
| [Resources.lean](Resources.lean), [lakefile.lean](lakefile.lean) | `Resources.lean` is the default build target and imports every specification module; the lakefile defines the `Resources`, `VmMemory`, `Utils`, and `Syscalls` libraries. |
| [Makefile](Makefile), [scripts/](scripts/) | Extraction (`make extract`, `make aeneas-bin`) and running Charon in crosvm's development container. |
| [FIXED_BUGS.md](FIXED_BUGS.md) | Fixed crosvm bugs and their upstream CLs. |

# Editing rules

- Keep generated Lean reproducible. Change Rust, extraction configuration, or
  the translator as appropriate, then regenerate; do not hand-edit generated
  definitions to make a proof succeed.
- Keep proofs in handwritten specification modules. Maintain external models
  in the handwritten `TypesExternal.lean`, `FunsExternal.lean`, and
  `Utils/CoreExternal.lean`; do not overwrite them with the generated templates.
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
- For known crosvm bugs, keep the pinned Rust source unchanged and add explicit
  hypotheses excluding the bug. Mark these with `TODO(BUG-...)`, naming the fix
  and the need to regenerate Lean before removing the restriction.
- Follow the existing `f args ⦃ result => property ⦄` specifications and register
  reusable function specifications with `@[step]` where appropriate. Prefer
  composing proved specifications with `step`, then use `simp`, `simp_all`,
  `scalar_tac`, or `omega` for the remaining obligations. Search the local Aeneas
  library and existing proofs before adding duplicate helper lemmas.
- Make specification definitions modular as well as their proofs. For wrapper
  functions, compose existing outcome and borrow predicates in the order of the
  Rust helper calls, using named intermediate values and states. For example,
  reuse `PciAllocatorBorrow` and `AlignedAllocationOutcome` for PCI allocation,
  and express the final state through the borrow's `back` function.
- State each helper's mathematical contract once. Reuse its success and error
  cases, invariants, and guarantees about unchanged state instead of repeating
  their definitions in callers. Add only the caller's policy, result conversion,
  and connections between intermediate states. Keep bounds needed solely to
  justify casts or arithmetic inside the proof when they follow from the contract.
- Use encapsulated results as much as possible. When the Rust code delegates a
  check to a library operation, state the outcome through that operation's
  result instead of restating its condition by hand. For example, for
  `size.checked_add(align as usize)` write
  `Usize.checked_add size (UScalar.cast .Usize a) = none` (or `= some s`), not
  `Usize.max < size.val + a.val` (or `s.val = size.val + a.val`). Derive the
  arithmetic in a lemma, with any extra preconditions it needs, where a proof
  or corollary uses it.
- Introduce predicates for reusable concepts or to clarify composition; avoid
  overlapping predicates that restate the same behavior. Put reusable
  consequences in lemmas on the existing predicate, and keep implementation
  details in private proof helpers. Elementary specifications should describe
  mathematical behavior rather than mirror each implementation branch.
- Respect bounded Rust arithmetic. Use `U64.val` and `U64.max` to express
  mathematical bounds, and discharge overflow and underflow obligations.
  Distinguish an expected `Option.none` return from failure in Aeneas's `Result`.
- crosvm supports only 64-bit hosts. When a proof needs 64-bit `usize` (e.g. a
  lossless `u64 as usize` cast or `Usize.max = U64.max`), take `[Platform64]`
  from `Utils/Platform.lean` and use its lemmas. Place `[Platform64]` before any
  hypotheses. Do not add per-value fit hypotheses such as `x.val ≤ Usize.max`
  for `u64` values, and do not keep specifications generic over 32-bit hosts.
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

When a repository's documentation and its existing code disagree, follow the
conventions used in the existing code, and in your final reply point out each
inconsistency you found between the documentation and the code

# Local references

- [Getting started with Aeneas](aeneas/documentation/getting-started.md)
- [Proof strategies](aeneas/documentation/proof-strategies.md)
- [Tactics reference](aeneas/documentation/tactics-reference.md)
- [Tips and tricks](aeneas/documentation/tips-and-tricks.md)
- [Lean tutorial examples](aeneas/tests/lean/Tutorial/)
