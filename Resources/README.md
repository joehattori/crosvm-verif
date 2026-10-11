# Verification scope

`AddressRangeSpec.lean` specifies the extracted AddressRange operations.
`AddressAllocatorSpec.lean` starts allocator verification with
`AddressAllocator::new(pool, None, None)`.

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

Custom alignments, the general `new_from_list` entry point, and allocation and
release methods remain unverified. The proof follows the generated call from
`new` into `new_from_list`; it does not replace the constructor with a model.

# External models

`TypesExternal.lean` and `FunsExternal.lean` are part of the trust boundary.
The new definitions contain no axioms, but their correspondence to Rust's
standard library is assumed, not proved from its implementation:

- HashMap contents use Mathlib's `Finmap (fun _ : K => V)`, which enforces
  unique keys and ignores entry order. Only `HashMap::new` is modeled; it
  returns the empty finite map. Hashing and random seeds are unobserved.
  Future lookup/update wrappers must relate Rust key equality to Lean equality;
  iteration requires a separate model because `Finmap` forgets entry order.
- BTreeSet contents are an ascending list. `new` creates an empty set and
  `insert` uses Rust's supplied `Ord::cmp`, retaining an existing equal value.
  Ordering and uniqueness for arbitrary insertions require a lawful comparator
  and a valid input set. This constructor only inserts into an empty set, so
  it never invokes the comparator.
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
`make verify` to check all imported proofs. The extraction now includes
`crate::address_allocator::AddressAllocator::new` alongside AddressRange.

The enclosing crosvm Cargo workspace requires its pinned minijail submodule,
even when extracting only resources:

```sh
git -C crosvm submodule update --init third_party/minijail
```

On macOS, the current crosvm pin has an unrelated compile error in
`base/src/sys/macos/mod.rs`: `PlatformSyslog::new` returns `syslog::Error`,
where its trait requires `&'static syslog::Error`. The constructor translation
was regenerated with that return type temporarily corrected, then the file was
restored. AddressAllocator and AddressRange Rust sources were unchanged. Fresh
macOS extraction at this pin therefore requires the same build workaround;
checking the generated Lean with `make verify` does not.
