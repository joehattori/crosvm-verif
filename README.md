# crosvm-verif

Verify core components of crosvm using Aeneas and Lean.

## Build and extraction

Develop on Ubuntu or use the Docker workflow below. Run commands from the
repository root. Initialize the pinned source submodules after cloning:

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
lake env lean Resources/AddressRange/Spec.lean
```

`make` defaults to verification. It checks the existing Lean translation without
regenerating it or rebuilding the extractor.

### Regenerate from Rust

Extraction needs compatible Charon and Aeneas binaries. The following target
builds both from the pinned Aeneas submodule using Nix:

```sh
make aeneas-bin
```

Before extracting, consult the [extraction prerequisites](Resources/README.md#extraction-and-checks),
including the nested minijail submodule.

```sh
# Extract Rust to LLBC, then generate Lean.
make extract

# Force fresh LLBC and Lean after Rust or extraction configuration changes.
make -B extract
```

The extraction targets are `extract-resources` and `extract-vm-memory`;
`extract` runs both. GuestAddress is extracted from the real `vm_memory` crate.
To run extraction in crosvm's pinned Docker development environment:

```sh
# Start Docker first. Download the pinned crosvm image and build pinned Charon.
scripts/charon-devcontainer setup
# Compile Rust in the container, then translate LLBC with the host Aeneas binary.
make -B extract-vm-memory CHARON="$PWD/scripts/charon-devcontainer"
make verify
```

The wrapper mounts this checkout at the same path inside the container and keeps
Rust toolchains and build caches in the container. Run `setup` again after a
Charon pin change. Charon is built from a clean archive of `aeneas/charon-pin`,
leaving local toolchain edits untouched. It does not modify either source
submodule. The host still needs the pinned Aeneas binary and Lean dependencies.

The LLBC targets currently have no Rust source prerequisites, so ordinary
`make extract` reuses existing `llbc/resources.llbc` and `llbc/vm_memory.llbc`.
Forced extraction is needed when the Rust input, toolchain, or extraction
options change.

The default binaries are `aeneas-bin/bin/charon` and `aeneas-bin/bin/aeneas`.
The Makefile supports `AENEAS_BIN`, `CHARON`, and `AENEAS` overrides and obtains
the Rust toolchain path from Charon.
