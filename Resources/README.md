# Verification scope

`AddressRangeSpec.lean` specifies the extracted AddressRange operations.
`AddressAllocatorSpec.lean` verifies `AddressAllocator::new(pool, None, None)`
and the private `internal_allocate_from_slot` update helper.

`non_overlapping_ranges_spec` characterizes the remainders by address membership:
their union is exactly `self \ other`, and they are disjoint whenever `other`
is nonempty. The union property holds for empty inputs too, but removing an
empty range can produce [overlapping remainders](../FIXED_BUGS.md#bug-001-overlapping-remainders-for-empty-ranges).
The allocator proof uses this single specification to show that the remainders
stay within the selected slot
and are disjoint from each other and the other free regions.

`new_default_spec` proves successful construction for every input range:

- Both alignments are four.
- There are no allocations.
- The stored pools and free regions contain just the input pool if it is
  nonempty, and are empty otherwise.

The specification uses `initialState` to state the exact field values, including
equality of both `a.pools.val` and `a.regions` to `initialPools pool`. These
equalities already determine which addresses are initially free. This is a
constructor postcondition; allocation and release change the free regions.

Empty inputs succeed, despite the Rust constructor's documentation suggesting
an error. No bound on the endpoints beyond their `u64` type is needed.

`internal_allocate_from_slot_spec` requires nonempty, ordered, disjoint free
regions, a slot belonging to those regions, and a nonempty requested range
contained in that slot. It proves:

- Success with the requested range's start address, including safety of the
  assertion that the slot was present.
- Preservation of the pools and both alignment fields.
- Exactly the finite-map update `insert allocation (range, tag) self.allocs`.
- Preservation of nonempty, ordered, disjoint free regions.
- An address is free afterward exactly when it was free before and is outside
  the requested range.

Nonemptiness and containment (`hn` and `hsub`) are caller obligations in the
specification; the helper does not validate them at runtime.

The helper also does not check key freshness: an existing key is replaced.
Using a fresh key preserves every prior allocation. It also does not enforce
alignment; the proof works for any alignment fields and leaves them unchanged.
`initialState.validRegions` connects the constructor postcondition to the
free-region invariant in `AddressAllocatorCollections.lean`.

Custom constructor alignments, the general `new_from_list` entry point, public
allocation methods (including aligned slot selection), and release methods
remain unverified. A full lifetime invariant relating allocations to the pools
is not yet proved. Both function proofs follow the generated Rust translation;
the constructor proof follows its call into `new_from_list`.

# External models

`TypesExternal.lean` and `FunsExternal.lean` are part of the trust boundary.
The new definitions contain no axioms, but their correspondence to Rust's
standard library is assumed, not proved from its implementation:

- HashMap contents use Mathlib's `Finmap (fun _ : K => V)`, which enforces
  unique keys and ignores entry order. `new` returns the empty map; `insert`
  updates a key and returns the previous value. The model assumes lawful,
  terminating Rust equality and hashing, with key equality matching Lean
  equality. `Alloc.eq_spec` proves the equality correspondence for allocator
  keys. Hashing, random seeds, and their implementation costs are unobserved.
  The extracted hash dictionaries are never called by the map model; their
  otherwise unsupported operations explicitly fail and introduce no axioms.
  This does not verify direct hash computations. Iteration requires a separate
  model because `Finmap` forgets entry order.
- BTreeSet contents are an ascending list. `new` creates an empty set and
  `insert` uses Rust's supplied `Ord::cmp`, retaining an existing equal value.
  `remove` uses the borrowed-key comparator and returns whether it removed a
  matching element. Borrowed and owned key orderings must agree. The helper
  uses identity borrowing. Collection proofs establish removal and disjoint
  insertion for valid free-region lists, using the translated AddressRange
  comparator. Empty ranges are excluded by this invariant, so Rust comparison
  equality agrees with Lean structure equality there.
- Filter stores its iterator and mutable predicate. `next` repeatedly advances
  the iterator and invokes the predicate, preserving its state on rejection.
  This can diverge for an infinite iterator rejecting every element. The proof
  establishes termination for the constructor's empty/singleton iterator.
- Storage layout, capacity, allocator behavior, and allocation failure are
  abstracted away, as in Aeneas's existing vector model.

The pinned backend's Iterator trait lacks `filter` and `collect` fields.
Extraction uses `-filter-trait-methods` to omit unsupported instance fields.
`collect` already has a default model in Aeneas; the handwritten `filter`
bridge supplies the default used by `Vec::IntoIter`. It does not justify calls
through arbitrary iterators overriding that method. The extractor still emits
two warnings about the absent fields; the resulting Lean is checked by the
build.

Generated `_Template.lean` files are references only and are not imported.
Their placeholder axioms, including the unused MaybeUninit declaration, do not
provide implementations. The existing formatting axiom is also not used by
the allocator proofs. Audit dependencies with `#print axioms` rather than
inferring their absence from a successful build.

# Extraction and checks

From the repository root, run `make -B extract` to regenerate from Rust and
`make verify` to check all imported proofs. Extraction includes AddressRange,
`AddressAllocator::new`, and `AddressAllocator::internal_allocate_from_slot`.

The Aeneas checkout includes a Lean name-generation fix that reserves the roots
of qualified names when naming local variables and generic parameters. This
allows crosvm's original `alloc` parameter in `internal_allocate_from_slot`:
the translator names it `alloc1` to avoid shadowing Lean's `alloc` namespace.
Rebuild Aeneas from this checkout before extracting (`make aeneas-bin`, or pass
the rebuilt binary with `make extract AENEAS=/path/to/aeneas`). The unmodified
prebuilt translator does not include this fix.

The enclosing crosvm Cargo workspace requires its pinned minijail submodule,
even when extracting only resources:

```sh
git -C crosvm submodule update --init third_party/minijail
```

On macOS, the current crosvm pin has an unrelated compile error in
`base/src/sys/macos/mod.rs`: `PlatformSyslog::new` returns `syslog::Error`,
where its trait requires `&'static syslog::Error`. The translation
was regenerated with that return type temporarily corrected, then the file was
restored. The crosvm checkout has no remaining source changes. Fresh macOS
extraction at this pin therefore requires the same build workaround;
checking the generated Lean with `make verify` does not.
