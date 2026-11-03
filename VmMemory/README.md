# VmMemory verification

The default build imports every `*/Spec.lean` module here; each states its exact
contracts and preconditions. The root Makefile lists the extracted functions.
`MemoryMapping` is verified against the `mmap(2)` and `munmap(2)` contracts in
[Syscalls/Mmap.lean](../Syscalls/Mmap.lean), and the `SharedMemory` size bound
against the `ftruncate(2)` contract in [Syscalls/Memfd.lean](../Syscalls/Memfd.lean).

Not verified:
- Guest-memory access, descriptor cloning, formatting, and serialization.
- `FileBackedMappingParameters::open`, modeled by an opaque result.

See the root README for [build and extraction](../README.md#build-and-extraction)
and the [trust boundary](../README.md#trust-boundary).
