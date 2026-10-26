# VmMemory verification

The default build checks both specification modules:

- [GuestAddress/Spec.lean](GuestAddress/Spec.lean): all inherent methods,
  explicit non-formatting trait methods, and the inherited `lt`, `le`, and `ge`
  comparisons used by `MemoryRegion`.
- [MemoryRegion/Spec.lean](MemoryRegion/Spec.lean): `start`, `end`, `contains`,
  and the Linux/Android `contains_range` method.

The specifications define the exact contracts and preconditions. The
non-overflow corollaries require `ValidBounds`. Constructors, the remaining
inherited trait defaults, formatting, serialization, and guest-memory access
are outside the verified scope.

See the root README for [build and extraction commands](../README.md#build-and-extraction)
and the project-wide [trust boundary](../README.md#trust-boundary). The
extraction slice is configured in the root Makefile; force `extract-vm-memory`
after changing its inputs.
