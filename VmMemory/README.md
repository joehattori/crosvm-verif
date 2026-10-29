# VmMemory verification

The default build imports every `*/Spec.lean` module here; each states its exact
contracts and preconditions. The root Makefile lists the extracted functions.
`MemoryMapping` is verified against the `mmap(2)` and `munmap(2)` contracts in
[Syscalls/Mmap.lean](../Syscalls/Mmap.lean).

Not verified:
- `GuestMemory::find_region`, `offset_from_base`, and `end_addr`: the pinned
  translator rejects `Iter::find` and method items passed as closures
  (higher-ranked signatures), and closures that return borrows into regions.
- `GuestMemory` constructors, guest-memory access, descriptor cloning,
  formatting, and serialization.

See the root README for [build and extraction](../README.md#build-and-extraction)
and the [trust boundary](../README.md#trust-boundary).
