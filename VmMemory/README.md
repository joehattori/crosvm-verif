# VmMemory verification

The default build checks these specification modules:

- [GuestAddress/Spec.lean](GuestAddress/Spec.lean): all inherent methods,
  explicit non-formatting trait methods, and the inherited `lt`, `le`, and `ge`
  comparisons used by `MemoryRegion`.
- [MemoryRegion/Spec.lean](MemoryRegion/Spec.lean): `start`, `end`, `contains`,
  the Linux/Android `contains_range` method, and the `new_from_shm` and
  `new_from_file` constructors, composed from the `MemoryMappingBuilder`
  specifications.
- [MemoryMapping/Spec.lean](MemoryMapping/Spec.lean): `i32::from(Protection)`
  and Linux `MemoryMapping` (`new_protection`,
  `from_fd_offset_protection_populate`, `try_mmap`, and `try_mmap_populate`),
  verified against the `mmap(2)` and `munmap(2)` specifications in
  [Syscalls/Mmap.lean](../Syscalls/Mmap.lean) and auxiliary syscall contracts.
- [MemoryMappingBuilder/Spec.lean](MemoryMappingBuilder/Spec.lean): `new`,
  `from_file`, `from_shared_memory`, `offset`, `build`, and the `wrap(_, None)`
  path, extracted through `vm_memory` from its `base` dependency for Linux.
- [GuestMemory/Spec.lean](GuestMemory/Spec.lean): the `WellFormed` region
  invariant (representable ends; each region ends before every later one starts)
  and its consequences: sorted bases, at most one region per address, and a total
  length that fits in `u64`. Verified methods: `locked`, `use_punchhole_locked`,
  `num_regions`, `address_in_range`, `range_overlap`, `is_valid_range`, and
  `checked_offset`, each with its mathematical form under `WellFormed`.

The specifications define the exact contracts and preconditions. The
non-overflow corollaries require `ValidBounds`. The remaining MemoryRegion
constructors, the remaining inherited trait defaults, descriptor cloning,
formatting, serialization, and guest-memory access are outside the verified
scope.

See the root README for [build and extraction commands](../README.md#build-and-extraction)
and the project-wide [trust boundary](../README.md#trust-boundary). The
extraction slice is configured in the root Makefile; force `extract-vm-memory`
after changing its inputs.
