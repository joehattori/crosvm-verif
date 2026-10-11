# crosvm-verif

This project uses Aeneas to prove properties of crosvm's Rust code in Lean.

The current extraction targets are `resources::address_range` and
`AddressAllocator::new` with its dependencies. The allocator proof covers default
alignments only. This is not a proof of all of crosvm; see
[verification scope and model assumptions](Resources/README.md) for the
properties established and the remaining limitations.

## Build and extraction

Run commands from the repository root. Initialize the pinned source submodules
after cloning:

```sh
git submodule update --init crosvm aeneas
```

### Check Lean

Lean and Lake must be available at the version specified by `lean-toolchain`.

```sh
# Check the Lean library and all imported specifications.
make verify
# Equivalent: lake build

# Check one proof file during development, with its imports already built.
lake env lean Resources/AddressRangeSpec.lean
```

`make` defaults to verification. It checks the existing Lean translation without
regenerating it or rebuilding the extractor.

### Regenerate from Rust

Extraction needs compatible Charon and Aeneas binaries. The following target
builds both from the pinned Aeneas submodule using Nix:

```sh
make aeneas-bin
```

Before extracting, consult the [extraction prerequisites and platform
notes](Resources/README.md#extraction-and-checks), including the nested minijail
submodule and the current macOS build workaround.

```sh
# Extract Rust to LLBC, then generate Lean.
make extract

# Force fresh LLBC and Lean after Rust or extraction configuration changes.
make -B extract
```

The LLBC target currently has no Rust source prerequisites, so ordinary
`make extract` reuses `llbc/resources.llbc` if it exists. Forced extraction is
needed when the Rust input, toolchain, or extraction options change.

The default binaries are `aeneas-bin/bin/charon` and `aeneas-bin/bin/aeneas`.
The Makefile supports `AENEAS_BIN`, `CHARON`, and `AENEAS` overrides and obtains
the Rust toolchain path from Charon.
