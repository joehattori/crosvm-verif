# Verification scope

Verification covers selected operations on
[AddressRange](AddressRange/Spec.lean),
[AddressAllocator](AddressAllocator/Spec.lean),
[AddressAllocatorSet](AddressAllocatorSet/Spec.lean), and
[SystemAllocator](SystemAllocator/Spec.lean). These specification modules define
the exact coverage, guarantees, and preconditions.

The default build also checks the `vm_memory` specifications; see
[VmMemory](../VmMemory/README.md).

The pinned crosvm revision includes the [upstream bug fixes](../FIXED_BUGS.md).

# Extraction and checks

See the top-level README for [commands](../README.md#build-and-extraction) and the
project-wide [trust boundary](../README.md#trust-boundary).

- Build Aeneas and Charon from the pinned checkouts; extraction depends on fixes
  included there.
- Initialize crosvm's nested dependency with
  `git -C crosvm submodule update --init third_party/minijail`.
