# Verification scope

Verification covers selected operations on
[AddressRange](AddressRange/Spec.lean),
[AddressAllocator](AddressAllocator/Spec.lean),
[AddressAllocatorSet](AddressAllocatorSet/Spec.lean), and
[SystemAllocator](SystemAllocator/Spec.lean). These specification modules define
the exact coverage, guarantees, and preconditions.

The default build also checks all inherent `GuestAddress` methods and its
explicit non-formatting trait methods; see [VmMemory](../VmMemory/README.md)
for coverage, assumptions, and extraction details.

The pinned crosvm revision includes the [upstream bug fixes](../FIXED_BUGS.md).

# Assumptions and limitations

The handwritten [external types](TypesExternal.lean) and
[functions](FunsExternal.lean) are part of the trust boundary: their correspondence
to Rust's standard library is assumed. Storage layout and allocation failure are
abstracted away, and the host page-size query is not verified. See the models for
supported operations and their limitations.

# Extraction and checks

See the [top-level README](../README.md#build-and-extraction) for commands.

- Build Aeneas and Charon from the pinned checkouts; extraction depends on fixes
  included there.
- Initialize crosvm's nested dependency with
  `git -C crosvm submodule update --init third_party/minijail`.
