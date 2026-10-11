# Purpose and scope

Use Aeneas to prove properties of crosvm's Rust code in Lean. The pipeline is
Rust → Charon LLBC → Aeneas-generated Lean → handwritten specifications and proofs.
The current extraction targets are `resources::address_range` and
`AddressAllocator::new` with its dependencies; this is not a proof of all of
crosvm. Keep claims tied to the functions, assumptions, and properties actually
verified. The allocator proof currently covers default alignments only.

# Repository map

- `crosvm/`: pinned upstream Rust submodule. The current source of interest is
  `crosvm/resources/src/address_range.rs` and `address_allocator.rs`.
- `aeneas/`: pinned toolchain submodule, including the Lean library at
  `aeneas/backends/lean/` and examples at `aeneas/tests/lean/`.
- `Resources/Types.lean` and `Resources/Funs.lean`: generated types and functions.
- `Resources/FunsExternal_Template.lean`: generated declarations for missing
  external models; a reference for maintaining the handwritten implementation.
- `Resources/FunsExternal.lean`: handwritten models of external Rust functions.
- `Resources/TypesExternal.lean`: handwritten collection and iterator models.
- `Resources/AddressRangeSpec.lean`: mathematical predicates and function proofs.
- `Resources/AddressAllocatorSpec.lean`: constructor initialization proofs.
- `Resources/README.md`: verified scope, model assumptions, and extraction notes.
- `Resources.lean`: library entry point. Import new specification modules here so
  the default build checks them.
- `Makefile`: toolchain build, extraction, and verification commands.
- `lakefile.lean`, `lake-manifest.json`, and `lean-toolchain`: Lean dependencies
  and version pins. Use these pins; avoid incidental dependency upgrades.

# Build and extraction

Run commands from the repository root.

```sh
# Check the Lean library and its imported specifications.
make verify
# Equivalent: lake build

# Check one proof file during development, with its imports already built.
lake env lean Resources/AddressRangeSpec.lean

# Build Aeneas and Charon using Nix when extraction binaries are needed.
make aeneas-bin

# Extract Rust to LLBC, then generate Lean.
make extract

# Force fresh LLBC and Lean after Rust or extraction configuration changes.
make -B extract
```

`make` defaults to verification; it does not regenerate the Lean translation.
The LLBC target currently has no Rust source prerequisites, so ordinary
`make extract` reuses `llbc/resources.llbc` if it exists. Force extraction when
the Rust input, toolchain, or extraction options change.

The default binaries are `aeneas-bin/bin/charon` and `aeneas-bin/bin/aeneas`.
The Makefile supports `AENEAS_BIN`, `CHARON`, and `AENEAS` overrides and obtains
the Rust toolchain path from Charon. Keep Charon and Aeneas compatible; use the
Makefile's extraction flags rather than inventing a separate invocation.
Proof-only work on checked-in Lean does not require rebuilding the extractor.

# Editing rules

- Keep generated Lean reproducible. Change Rust, extraction configuration, or
  the translator as appropriate, then regenerate; do not hand-edit generated
  definitions to make a proof succeed.
- Keep proofs in handwritten specification modules. Maintain external models
  in `FunsExternal.lean`; do not overwrite it with the generated template.
  After extraction, reconcile any changed template signatures and inspect the
  generated diff before updating proofs.
- Treat both submodules as pinned dependencies. Modify their contents or
  revisions only when needed for the requested task, and report those changes.
  For work inside crosvm, consult `crosvm/.agents/AGENTS.md` and its contribution
  workflow. For Aeneas changes, consult `aeneas/CLAUDE.md` and relevant local docs.
- Keep `.lake/`, `aeneas-bin`, and `llbc/` build artifacts out of commits.

# Proof standards

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
  and make assumptions explicit. `FunsExternal.lean` currently contains the
  formatting axiom `U64.Insts.CoreFmtLowerHex.fmt`; the generated template also
  contains placeholder axioms. Do not treat those declarations as proved
  behavior. Use `#print axioms theoremName` when auditing theorem dependencies.

# Validation and reporting

After changing Lean proofs or models, run `make verify` and inspect warnings as
well as errors. After changing extraction inputs, regenerate first and then
verify. If Rust code changes, also run the relevant crosvm checks according to
its contribution workflow. Documentation-only changes need path and command
consistency checks, not a toolchain rebuild.

Report the properties proved, files changed, commands run and their outcomes,
and any remaining assumptions or unverified steps. Distinguish checking the
committed Lean translation from validating a freshly regenerated translation.

# Local references

- `aeneas/documentation/getting-started.md`
- `aeneas/documentation/proof-strategies.md`
- `aeneas/documentation/tactics-reference.md`
- `aeneas/documentation/tips-and-tricks.md`
- `aeneas/tests/lean/Tutorial/`
