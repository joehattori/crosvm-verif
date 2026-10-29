# crosvm-verif

Verify core components of crosvm using Aeneas and Lean.

## Trust boundary

Lean checks proofs about the translated models. Applying those results to Rust
relies on Rust compilation, Charon/Aeneas translation, and the correspondence of
Aeneas's standard-library models and this project's handwritten external models
to their Rust implementations. Exact coverage and preconditions are defined in
the specification modules linked from [Resources](Resources/README.md) and
[VmMemory](VmMemory/README.md).

The handwritten `TypesExternal.lean` and `FunsExternal.lean` files are part of
the trust boundary: [Resources types](Resources/TypesExternal.lean),
[Resources functions](Resources/FunsExternal.lean),
[VmMemory types](VmMemory/TypesExternal.lean), and
[VmMemory functions](VmMemory/FunsExternal.lean). See those files for their
models and assumptions. Models of Rust core items used by both crates, which
Aeneas names without a crate prefix, are shared in
[Utils/CoreExternal.lean](Utils/CoreExternal.lean).

The specifications describe the values returned by the translated functions.
Aeneas does not translate `Drop` implementations, so implicit drops, such as
`munmap` in `MemoryMapping::drop`, are not modeled; explicit system calls in
function bodies are. `Arc<T>` is modeled by its contents, without reference
counts, allocation identity, or drop timing. Resource lifetimes and leaks are
outside the verified scope.

crosvm supports only 64-bit hosts, but the generated Lean leaves the width of
`usize` unspecified. Specifications that depend on 64-bit `usize` take the
explicit assumption `[Platform64]` ([Utils/Platform.lean](Utils/Platform.lean)).

## Build and extraction

Develop on Linux or use the Docker workflow below. Run commands from the
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
`extract` runs both. GuestAddress, the selected MemoryRegion methods, the
Linux `MemoryMapping` mapping constructors (`new_protection`,
`from_fd_offset_protection_populate`, `try_mmap`, and `try_mmap_populate`),
and the MemoryMappingBuilder configuration, `build`, and `wrap` methods are
extracted from the real `vm_memory` crate and its `base` dependency.
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
