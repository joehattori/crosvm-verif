# Verification scope

- [AddressRange](AddressRange/Spec.lean): extracted range operations.
- [AddressAllocator](AddressAllocator/Spec.lean): construction from a single pool
  or a vector of pools,
  slot allocation, free-region insertion with neighbor coalescing, fixed-address
  allocation, and forward/reverse allocation with explicit alignment or
  preferred-alignment fallback, release by key or containing address, and PCI
  offset lookup, subject to the stated preconditions. Construction and public
  allocation/release operations preserve pool accounting and disjointness.
- [AddressAllocatorSet](AddressAllocatorSet/Spec.lean): construction preserves
  the allocator slice, including order and component states, and mutable borrow
  write-back returns the final set's slice. Empty slices are supported; construction
  does not require or establish component well-formedness. PCI offset lookup returns
  the first successful component result in slice order, or the last component's
  error if all reject the request (`OutOfSpace` for an empty set). Lookup reuses
  the single-allocator bounds contract and requires neither component
  well-formedness nor unique allocation keys across the set.
  Allocation tries components in order with each component's preferred-alignment
  fallback, updates only the first successful component, and preserves component
  well-formedness. If all attempts fail, the set is unchanged and the last error
  is returned; an empty set returns `OutOfSpace`. Any component error permits the
  next attempt. Allocation assumes component well-formedness, without requiring
  disjoint pools or unique allocation keys across components.
- [SystemAllocator](SystemAllocator/Spec.lean): construction, including initial
  resource pools, component well-formedness, and configuration errors; anonymous
  allocation ID generation, IRQ/GPE allocation and IRQ reservation until counter
  exhaustion, IRQ release, PCI bus allocator presence checks, lookup and creation
  with mutable borrow write-back, PCI slot allocation with preferred alignment
  and function fallback, PCI slot reservation and release, and MMIO allocation
  from the low or high space with the requested alignment and search direction;
  public MMIO allocation's address-limit rejection, prefetchability-based space
  selection, and high-to-low fallback only on `OutOfSpace`. MMIO allocation preserves
  component invariants and leaves the system unchanged on errors.

The internal free-region insertion helper is specified for intermediate states;
the full accounting invariant is restored by the enclosing release operation.

# Assumptions and limitations

The Lean specifications state the precise guarantees and preconditions.
The pinned crosvm revision includes the [upstream bug fixes](../FIXED_BUGS.md).
System allocator construction assumes disjoint MMIO restrictions and a
successful host page-size query.
Public MMIO allocation respects the requested maximum address when the low
MMIO pool contains only addresses at most `u32::MAX`, as documented by the Rust
configuration API. This pool bound is an explicit hypothesis: the constructor
and component well-formedness do not enforce it. Requests with a maximum below
`u32::MAX` return `OutOfSpace` without changing the system.

The handwritten [external types](TypesExternal.lean) and
[functions](FunsExternal.lean) are part of the trust boundary: their correspondence
to Rust's standard library is assumed. Storage layout and allocation failure are
abstracted away. Generated `_Template.lean` files are not imported.
Hash-map iteration uses an arbitrary enumeration of the finite-map entries;
the overlap specification accepts any conflicting key.
The page-size result is opaque and supplied as a theorem hypothesis; the host OS
query is not verified. The B-tree map model supports construction, key presence
checks, and entry value borrows with lawful, total comparators and consistent
borrowed-key ordering; ordered traversal is not modeled.
Optional mutable-reference branching models both the selected value and its
borrow write-back.
String conversion models UTF-8 `str` contents; general formatting is unsupported.

# Extraction and checks

See the [top-level README](../README.md#build-and-extraction) for commands.

- Build Aeneas from the working checkout, which includes the allocator's required
  name-generation and shared-borrow join fixes, including preservation of frozen
  mutable borrows when preparing shared loans for loop joins, distinct names for
  specialized default methods, and shared references to external trait models.
- Initialize crosvm's nested dependency with
  `git -C crosvm submodule update --init third_party/minijail`.
- On macOS, the current crosvm pin needs a build workaround:
  `PlatformSyslog::new` in `base/src/sys/macos/mod.rs` must return
  `&'static syslog::Error`. Apply this only in a temporary copy and pass its
  `resources/Cargo.toml` through `RESOURCES_MANIFEST` when extracting. Checking
  the existing Lean translation does not need this workaround.
