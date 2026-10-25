# Verification scope

- [AddressRange](AddressRange/Spec.lean): extracted range operations.
- [AddressAllocator](AddressAllocator/Spec.lean): construction from a single pool
  or a vector of pools,
  slot allocation, free-region insertion with neighbor coalescing, fixed-address
  allocation, and forward/reverse allocation with explicit alignment or
  preferred-alignment fallback, release by key or containing address, allocation
  lookup, and PCI offset lookup, subject to the stated preconditions. Construction
  and public allocation/release operations preserve pool accounting and disjointness.
- [AddressAllocatorSet](AddressAllocatorSet/Spec.lean): construction preserves
  the allocator slice, including order and component states, and mutable borrow
  write-back returns the final set's slice. Lookup returns the exact range and tag
  from the first allocator containing the key, or `None` exactly when all allocators
  lack the key. Empty slices and keys present in multiple allocators are supported;
  construction and lookup require no component well-formedness assumption, and
  construction does not establish it.
  PCI offset lookup returns the first successful component result in slice order,
  or the last component's error if all reject the request (`OutOfSpace` for an empty
  set). This lookup reuses the single-allocator bounds contract and requires
  neither component well-formedness nor unique allocation keys across the set.
  Allocation tries components in order with each component's preferred-alignment
  fallback, updates only the first successful component, and preserves component
  well-formedness. If all attempts fail, the set is unchanged and the last error
  is returned; an empty set returns `OutOfSpace`. Any component error permits the
  next attempt. Allocation assumes component well-formedness, without requiring
  disjoint pools or unique allocation keys across components.
  Fixed-address allocation also updates only the first successful component and
  preserves component well-formedness, leaving the entire set unchanged on errors
  and returning the last error (`OutOfSpace` for an empty set). Success is equivalent
  to some component having a fresh key and a free slot containing the entire
  nonempty request; no disjoint pools or distinct keys across components are required.
  Release tries components in order, stops at the first success, and preserves
  component well-formedness, slice length, pools, and alignments. Failed attempts
  retain their component state changes; the suffix after success is unchanged.
  Exhaustion returns the last error, or `OutOfSpace` for an empty set. A key absent
  from every component leaves the set unchanged and returns `BadAlloc` when the
  set is nonempty.
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
  `mmio_allocator_any` always returns the low and high MMIO allocators in that
  order, with their complete states. Returning a two-component set writes both
  components back in order and preserves every other system field; returning the
  original set leaves the system unchanged. Borrowing requires no well-formedness
  assumption, and writing back well-formed components preserves system
  well-formedness. The write-back contract requires the original slice length of
  two, as fixed by the Rust MMIO array.
  `mmio_pools` returns all configured pools in low-then-high allocator order,
  preserving each component's pool order, empty ranges, and duplicates. Its
  specification requires the combined list length to fit `usize`; it does not
  require component well-formedness.

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
The forward `FlatMap` model drains each inner iterator in order, skips exhausted
inners, and stops polling the outer iterator after its first `None`. It preserves
closure state and propagates failures. Reverse iteration is not modeled.

Set release assumes each component is well-formed, without requiring allocation
keys to be unique across components. It composes the single-allocator release
contract, including removal of empty allocation records on `AllocSizeZero` errors.

# Extraction and checks

See the [top-level README](../README.md#build-and-extraction) for commands.

- Build Aeneas from the working checkout, which includes the allocator's required
  name-generation, shared-borrow join, and unused iterator-trait cleanup fixes,
  including preservation of frozen mutable borrows when preparing shared loans
  for loop joins.
- Build Charon from the working checkout as well: MMIO pool extraction needs its
  closure-lifetime repair, which recovers argument/return outlives relationships
  from rustc's borrow-checker facts before MIR extraction consumes the bodies.
- Initialize crosvm's nested dependency with
  `git -C crosvm submodule update --init third_party/minijail`.
- On macOS, the current crosvm pin needs a build workaround:
  `PlatformSyslog::new` in `base/src/sys/macos/mod.rs` must return
  `&'static syslog::Error`. Apply this only in a temporary copy and pass its
  `resources/Cargo.toml` through `RESOURCES_MANIFEST` when extracting. Checking
  the existing Lean translation does not need this workaround.
