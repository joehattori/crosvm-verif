# Verification scope

- [AddressRange](AddressRange/Spec.lean): extracted range operations.
- [AddressAllocator](AddressAllocator/Spec.lean): single-pool construction,
  slot allocation, free-region insertion with neighbor coalescing, fixed-address
  allocation, and forward/reverse allocation with explicit alignment or
  preferred-alignment fallback, plus release by key or containing address,
  subject to the stated well-formedness and arithmetic assumptions.

Multi-pool construction and full accounting between pools, free regions, and
allocations remain unverified.

# Assumptions and limitations

The Lean specifications state the precise guarantees and preconditions.
Restrictions caused by [known bugs](../FIXED_BUGS.md) are marked with
`TODO(BUG-...)`; the crosvm source remains unchanged.

The handwritten [external types](TypesExternal.lean) and
[functions](FunsExternal.lean) are part of the trust boundary: their correspondence
to Rust's standard library is assumed. Storage layout and allocation failure are
abstracted away. Generated `_Template.lean` files are not imported.
Hash-map iteration uses an arbitrary enumeration of the finite-map entries;
the overlap specification accepts any conflicting key.

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
