module
public import Aeneas
public import Mathlib.Data.Finmap
@[expose] public section
open Aeneas Aeneas.Std

/- These are logical models of external Rust types, not verified implementations
   of the standard library. Storage layout, capacity, allocation failure, and
   hash seeds are outside this model. Only the operations in FunsExternal are
   supported. The unused MaybeUninit template declaration needs no model. -/

@[rust_type "core::iter::adapters::filter::Filter"]
structure core.iter.adapters.filter.Filter (I P : Type) where
  iter : I
  predicate : P

/-- Finite map contents. Only empty construction is modeled so far; ordered
    traversal and comparator-based operations require separate models. -/
@[rust_type "alloc::collections::btree::map::BTreeMap"]
abbrev alloc.collections.btree.map.BTreeMap (K V _A : Type) :=
  Finmap (fun _ : K => V)

/-- Finite map contents with unique keys and no observable entry order. -/
@[rust_type "std::collections::hash::map::HashMap"]
abbrev std.collections.hash.map.HashMap (K V _S _A : Type) :=
  Finmap (fun _ : K => V)

/-- Remaining entries in an unspecified iteration order. -/
@[rust_type "std::collections::hash::map::Iter"]
abbrev std.collections.hash.map.Iter (K V : Type) := List (K × V)

@[rust_type "std::hash::random::RandomState"]
def std.hash.random.RandomState := Unit

/-- Ascending elements, with uniqueness determined by Rust's `Ord::cmp`.
    The invariant holds for states reachable through `new` and `insert` when
    the supplied comparator obeys the Rust `Ord` contract. -/
@[rust_type "alloc::collections::btree::set::BTreeSet"]
abbrev alloc.collections.btree.set.BTreeSet (T _A : Type) := List T

/-- Remaining elements in ascending order; front/back iteration consumes one end. -/
@[rust_type "alloc::collections::btree::set::Iter"]
abbrev alloc.collections.btree.set.Iter (T : Type) := List T

/-- Remaining elements of a bounded query, in ascending order. -/
@[rust_type "alloc::collections::btree::set::Range"]
abbrev alloc.collections.btree.set.Range (T : Type) := List T

/-- Hashing is unobserved by the finite-map model. Direct hasher operations are
    unsupported (fail explicitly); this is not a model of hash outputs. -/
@[rust_type "std::hash::random::DefaultHasher"]
def std.hash.random.DefaultHasher := Unit
