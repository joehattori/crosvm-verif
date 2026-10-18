# Verification scope

- [AddressRange](AddressRange/Spec.lean): extracted range operations.
- [AddressAllocator](AddressAllocator/Spec.lean): construction from a single pool
  or a vector of pools,
  slot allocation, free-region insertion with neighbor coalescing, fixed-address
  allocation, and forward/reverse allocation with explicit alignment or
  preferred-alignment fallback, release by key or containing address, and PCI
  offset lookup, subject to the stated preconditions.
- [SystemAllocator](SystemAllocator/Spec.lean): construction, including initial
  resource pools, component well-formedness, and configuration errors; anonymous
  allocation ID generation, IRQ allocation and reservation until counter exhaustion,
  and IRQ release.

Full accounting between pools, free regions, and allocations remains unverified.

# Assumptions and limitations

The Lean specifications state the precise guarantees and preconditions.
The pinned crosvm revision includes the [upstream bug fixes](../FIXED_BUGS.md).
System allocator construction assumes disjoint MMIO restrictions, a successful
host page-size query, and explicit bounds excluding unchecked reservation
arithmetic failures (`TODO(BUG-003)`).

The handwritten [external types](TypesExternal.lean) and
[functions](FunsExternal.lean) are part of the trust boundary: their correspondence
to Rust's standard library is assumed. Storage layout and allocation failure are
abstracted away. Generated `_Template.lean` files are not imported.
Hash-map iteration uses an arbitrary enumeration of the finite-map entries;
the overlap specification accepts any conflicting key.
The page-size result is opaque and supplied as a theorem hypothesis; the host OS
query is not verified. The B-tree map model currently supports only construction.
String conversion models UTF-8 `str` contents; general formatting is unsupported.

# Extraction and checks

See the [top-level README](../README.md#build-and-extraction) for commands.

- Build Aeneas from the working checkout, which includes the allocator's required
  name-generation and shared-borrow join fixes.
- Initialize crosvm's nested dependency with
  `git -C crosvm submodule update --init third_party/minijail`.
- On macOS, the current crosvm pin needs a build workaround:
  `PlatformSyslog::new` in `base/src/sys/macos/mod.rs` must return
  `&'static syslog::Error`. Apply this only in a temporary copy and pass its
  `resources/Cargo.toml` through `RESOURCES_MANIFEST` when extracting. Checking
  the existing Lean translation does not need this workaround.
