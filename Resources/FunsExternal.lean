-- External functions for [resources]
module
public import Aeneas
public import Resources.Types
public import Utils.CoreExternal
@[expose] public section
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.whitespace false
set_option linter.style.setOption false
set_option linter.style.longLine false

set_option maxHeartbeats 1000000
set_option maxRecDepth 2048
open resources

noncomputable instance : DecidableEq resources.Alloc := Classical.decEq _

/-- Supply a kernel-checked length bound for generated string literals instead
    of using the pinned `toStr` function's native-evaluation default. -/
macro "toStr" value:str : term =>
  `(Aeneas.Std.toStr $value (by simp only [Aeneas.Std.U32.max_eq]; decide +kernel))

/-- Rust's logical variant discriminants, independent of storage layout. -/
instance {T : Type _} : Discriminant (Option T) Isize where
  read_discriminant
    | none => 0#isize
    | some _ => 1#isize

/-- Direct formatting is unsupported. String conversion below copies UTF-8
    contents without using the opaque formatter model. -/
@[rust_fun "core::fmt::{core::fmt::Display<str>}::fmt"]
def Str.Insts.CoreFmtDisplay.fmt (_ : Str) (_ : core.fmt.Formatter) :
    Result (core.result.Result Unit core.fmt.Error × core.fmt.Formatter) :=
  fail .panic

/-- Only Rust's standard `str` conversion is supported. Other types and invalid
    UTF-8 fail explicitly; allocation failure is abstracted away. -/
@[rust_fun "alloc::string::{alloc::string::ToString<@T>}::to_string"]
noncomputable def alloc.string.ToString.Blanket.to_string {T : Type _}
    (display : core.fmt.Display T) (value : T) : Result String := by
  classical
  exact if h : T = Str then
    let str : Str := h ▸ value
    let display : core.fmt.Display Str := h ▸ display
    if display.fmt = Str.Insts.CoreFmtDisplay.fmt then
      Result.ofOption (String.fromUTF8? ⟨str.val.toArray.map (fun b => UInt8.ofBitVec b.bv)⟩) .panic
    else fail .panic
  else fail .panic

/-- Discard the error while preserving a successful value. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::ok"]
def core.result.Result.ok {T E : Type _} (self : core.result.Result T E) : Result (Option T) :=
  match self with
  | .Ok value => Std.Result.ok (some value)
  | .Err _ => Std.Result.ok none

/-- Reuse Aeneas's Result branching model under the extracted trait name. -/
@[simp, rust_fun "core::result::{core::ops::try_trait::Try<core::result::Result<@T, @E>, @T, core::result::Result<!, @E>>}::branch"]
abbrev core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch {T E : Type _}
    (self : core.result.Result T E) := core.result.Result.Insts.CoreOpsTry.branch self

@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>, @T, core::option::Option<!>>}::branch"]
def core.option.Option.Insts.CoreOpsTry_traitTryTOptionNever.branch {T : Type _} (self : Option T) :
    Result (core.ops.control_flow.ControlFlow (Option Never) T) :=
  match self with
  | some value => ok (.Continue value)
  | none => ok (.Break none)

/-- Branch on an optional mutable reference. The backward map carries the returned
    referent back through `Some`; the `None` branch has no borrowed value. -/
@[rust_fun "core::option::{core::ops::try_trait::Try<core::option::Option<@T>, @T, core::option::Option<!>>}::branch"]
def core.ops.try_trait.TryOptionMut0T0Mut0T0OptionNever.Blanket.branch {T0 : Type _} (self : Option T0) :
    Result ((core.ops.control_flow.ControlFlow (Option Never) T0) ×
      (core.ops.control_flow.ControlFlow (Option Never) T0 → Option T0)) :=
  let back := fun updated => match updated with
    | .Continue value => some value
    | .Break _ => none
  match self with
  | some value => ok (.Continue value, back)
  | none => ok (.Break none, back)

/-- Cloning preserves string contents; storage allocation is abstracted away. -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (self : String) : Result String :=
  ok self

/-- The non-strict relation of a pure comparator, used by the stable-sort model. -/
noncomputable def alloc.slice.sortLe {T F : Type _}
    (cmp : core.ops.function.FnMut F (T × T) Ordering) (closure : F) (x y : T) : Bool := by
  classical
  exact decide (cmp.call_mut closure (x, y) ≠ ok (.gt, closure))

/-- Stable sorting for pure, nonfailing total comparators. Stateful, failing, or
    inconsistent comparators are unsupported and fail explicitly. Merge sort
    preserves equal-key order, as Rust's `sort_by` requires; the Rust sorting
    algorithm and allocation failures are abstracted away. -/
@[rust_fun "alloc::slice::{[@T]}::sort_by"]
noncomputable def alloc.slice.Slice.sort_by {T F : Type _}
    (cmp : core.ops.function.FnMut F (T × T) Ordering) (self : Slice T) (closure : F) :
    Result (Slice T) := by
  classical
  let le := alloc.slice.sortLe cmp closure
  exact if
    (∀ x y, ∃ order, cmp.call_mut closure (x, y) = ok (order, closure) ∧
      cmp.call_mut closure (y, x) = ok (order.swap, closure)) ∧
    (∀ x y z, le x y → le y z → le x z)
  then ok (Slice.from (self.val.mergeSort le) (by simp))
  else fail .panic

/-- A shared vector iterator visits the original elements in order. The allocator
    parameter has no observable effect in the storage-independent vector model. -/
@[rust_fun
  "alloc::vec::{core::iter::traits::collect::IntoIterator<&'a alloc::vec::Vec<@T>, &'a @T, core::slice::iter::Iter<'a, @T>>}::into_iter"]
def SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter
    {T : Type _} (_A : Type _) (self : alloc.vec.Vec T) : Result (core.slice.iter.Iter T) :=
  ok ⟨alloc.vec.Vec.deref self, 0⟩

/-- [core::cmp::{impl core::cmp::PartialEq<core::cmp::Ordering> for core::cmp::Ordering}::eq]:
    Source: '/rustc/library/core/src/cmp.rs', lines 413:43-413:52
    Name pattern: [core::cmp::{core::cmp::PartialEq<core::cmp::Ordering, core::cmp::Ordering>}::eq]
    Visibility: public -/
@[rust_fun
  "core::cmp::{core::cmp::PartialEq<core::cmp::Ordering, core::cmp::Ordering>}::eq"]
def core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq
  (x y : Ordering) : Result Bool :=
  ok (decide (x = y))

/-- [core::cmp::{core::cmp::Ordering}::then_with]:
    Source: '/rustc/library/core/src/cmp.rs', lines 668:4-670:59
    Name pattern: [core::cmp::{core::cmp::Ordering}::then_with]
    Visibility: public -/
@[rust_fun "core::cmp::{core::cmp::Ordering}::then_with"]
def core.cmp.Ordering.then_with
  {F : Type _} (opsfunctionFnOnceFTupleOrderingInst : core.ops.function.FnOnce F
  Unit Ordering) (o : Ordering) (f : F) : Result Ordering :=
  match o with
  | .eq => opsfunctionFnOnceFTupleOrderingInst.call_once f ()
  | _ => ok o

/-- [core::fmt::num::{impl core::fmt::LowerHex for u64}::fmt]:
    Source: '/rustc/library/core/src/fmt/num.rs', lines 14:12-14:68
    Name pattern: [core::fmt::num::{core::fmt::LowerHex<u64>}::fmt]
    Visibility: public -/
@[rust_fun "core::fmt::num::{core::fmt::LowerHex<u64>}::fmt"]
axiom U64.Insts.CoreFmtLowerHex.fmt
  :
  Std.U64 → core.fmt.Formatter → Result ((core.result.Result Unit
    core.fmt.Error) × core.fmt.Formatter)

/-- [core::ops::range::{core::ops::range::RangeInclusive<Idx>}::start]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 425:4-425:37
    Name pattern: [core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::start]
    Visibility: public -/
@[rust_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::start"]
def core.ops.range.RangeInclusive.start
  {Idx : Type _} (r : core.ops.range.RangeInclusive Idx) : Result Idx :=
  ok r.start

/-- [core::ops::range::{core::ops::range::RangeInclusive<Idx>}::end]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 450:4-450:35
    Name pattern: [core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::end]
    Visibility: public -/
@[rust_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::end"]
def core.ops.range.RangeInclusive.end
  {Idx : Type _} (r : core.ops.range.RangeInclusive Idx) : Result Idx :=
  ok r.end

/-- Construct a lazy filter, preserving both the iterator and predicate state. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter"]
def core.iter.traits.iterator.Iterator.filter.default
  {I P T : Type _} (_iterInst : core.iter.traits.iterator.Iterator I T)
  (_predInst : core.ops.function.FnMut P T Bool)
  (iter : I) (predicate : P) : Result (core.iter.adapters.filter.Filter I P) :=
  ok ⟨iter, predicate⟩

/-- Compatibility with the pinned backend's Iterator model, which lacks a
    filter field. Rust's default method constructs the adapter above.
    The constructor uses Vec::IntoIter, which uses this default. This bridge
    does not model an arbitrary iterator overriding `filter`. -/
def Aeneas.Std.core.iter.traits.iterator.Iterator.filter
  {I P T : Type _} (iterInst : core.iter.traits.iterator.Iterator I T)
  (predInst : core.ops.function.FnMut P T Bool)
  (iter : I) (predicate : P) : Result (_root_.core.iter.adapters.filter.Filter I P) :=
  _root_.core.iter.traits.iterator.Iterator.filter.default iterInst predInst iter predicate

/-- Search until the next accepted element, keeping mutations of the predicate
    even when an element is rejected. Infinite rejection may diverge. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::next"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
  {I P T : Type _} (iterInst : core.iter.traits.iterator.Iterator I T)
  (predInst : core.ops.function.FnMut P T Bool)
  (self : core.iter.adapters.filter.Filter I P) :
  Result (Option T × core.iter.adapters.filter.Filter I P) := do
  let (item, iter) ← iterInst.next self.iter
  match item with
  | none => ok (none, ⟨iter, self.predicate⟩)
  | some value =>
    let (keep, predicate) ← predInst.call_mut self.predicate value
    if keep then ok (some value, ⟨iter, predicate⟩)
    else next iterInst predInst ⟨iter, predicate⟩
partial_fixpoint

@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new"]
def std.collections.hash.map.HashMapKVRandomStateGlobal.new (K V : Type _) :
  Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState alloc.alloc.Global) :=
  ok ∅

/-- Enumerate each entry once in an arbitrary order. The chosen order abstracts
    Rust's hash-table layout; specifications must not depend on that order. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::iter"]
noncomputable def std.collections.hash.map.HashMap.iter {K V S A : Type _}
    (self : std.collections.hash.map.HashMap K V S A) :
    Result (std.collections.hash.map.Iter K V) :=
  ok (self.entries.toList.map fun entry => (entry.1, entry.2))

@[rust_fun
  "std::collections::hash::map::{core::iter::traits::iterator::Iterator<std::collections::hash::map::Iter<'a, @K, @V>, (&'a @K, &'a @V)>}::next"]
def std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV.next
    {K V : Type _} : std.collections.hash.map.Iter K V →
      Result (Option (K × V) × std.collections.hash.map.Iter K V)
  | [] => ok (none, [])
  | entry :: rest => ok (some entry, rest)

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, alloc::alloc::Global>}::new"]
def alloc.collections.btree.set.BTreeSetTGlobal.new (T : Type _) :
  Result (alloc.collections.btree.set.BTreeSet T alloc.alloc.Global) :=
  ok []

/-- Insert in comparator order. An equal element retains the existing value,
    as in Rust's BTreeSet::insert (in contrast with replace). -/
def alloc.collections.btree.set.insertList {T : Type _} (ord : core.cmp.Ord T)
  (value : T) : List T → Result (Bool × List T)
  | [] => ok (true, [value])
  | head :: tail => do
    let ordering ← ord.cmp value head
    match ordering with
    | .lt => ok (true, value :: head :: tail)
    | .eq => ok (false, head :: tail)
    | .gt =>
      let (added, tail) ← insertList ord value tail
      ok (added, head :: tail)

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::insert"]
def alloc.collections.btree.set.BTreeSet.insert
  {T A : Type _} (_allocator : resources.core.alloc.AllocatorClone A) (ord : core.cmp.Ord T)
  (self : alloc.collections.btree.set.BTreeSet T A) (value : T) :
  Result (Bool × alloc.collections.btree.set.BTreeSet T A) :=
  alloc.collections.btree.set.insertList ord value self

@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type _} (value : T) : Result T := ok value

/-- Remove the first comparator-equal borrowed key. On a valid BTreeSet there
    is at most one such element. Borrowed and owned orderings must agree. -/
def alloc.collections.btree.set.removeList {T Q : Type _}
    (borrow : resources.core.borrow.Borrow T Q) (ord : core.cmp.Ord Q)
    (key : Q) : List T → Result (Bool × List T)
  | [] => ok (false, [])
  | head :: tail => do
    let borrowed ← borrow.borrow head
    let ordering ← ord.cmp key borrowed
    if ordering = .eq then ok (true, tail)
    else
      let (removed, rest) ← removeList borrow ord key tail
      ok (removed, head :: rest)

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::remove"]
def alloc.collections.btree.set.BTreeSet.remove
    {T A Q : Type _} (_allocator : resources.core.alloc.AllocatorClone A)
    (borrow : resources.core.borrow.Borrow T Q) (_ord : core.cmp.Ord T)
    (ordQ : core.cmp.Ord Q) (self : alloc.collections.btree.set.BTreeSet T A) (key : Q) :
    Result (Bool × alloc.collections.btree.set.BTreeSet T A) :=
  alloc.collections.btree.set.removeList borrow ordQ key self

/-- Finite-map insertion, including the old value returned on replacement.
    Rust key equality must coincide with Lean equality; hashes and storage are
    abstracted away, so the hash dictionaries are never called. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert"]
noncomputable def std.collections.hash.map.HashMap.insert
    {K V S A H : Type _} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (self : std.collections.hash.map.HashMap K V S A) (key : K) (value : V) :
    Result (Option V × std.collections.hash.map.HashMap K V S A) := by
  classical
  exact ok (Finmap.lookup key self, Finmap.insert key value self)

/- The following hash operations occur only in dictionaries passed to the
   abstract map. They deliberately fail rather than assert any hash behavior.
   No successful direct hash computation is modeled or verified. -/
def Isize.Insts.CoreHashHash.hash {H : Type _} (_ : core.hash.Hasher H)
    (_ : Isize) (_ : H) : Result H := fail .panic
def Usize.Insts.CoreHashHash.hash {H : Type _} (_ : core.hash.Hasher H)
    (_ : Usize) (_ : H) : Result H := fail .panic
def U8.Insts.CoreHashHash.hash {H : Type _} (_ : core.hash.Hasher H)
    (_ : U8) (_ : H) : Result H := fail .panic
def U64.Insts.CoreHashHash.hash {H : Type _} (_ : core.hash.Hasher H)
    (_ : U64) (_ : H) : Result H := fail .panic
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish
    (_ : std.hash.random.DefaultHasher) : Result U64 := fail .panic
def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write
    (_ : std.hash.random.DefaultHasher) (_ : Slice U8) :
    Result std.hash.random.DefaultHasher := fail .panic
def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher
    (_ : std.hash.random.RandomState) : Result std.hash.random.DefaultHasher := fail .panic

/-- Search the remaining iterator, preserving predicate mutations between calls. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::find"]
def core.iter.traits.iterator.Iterator.find.default
    {I P T : Type _} (iterInst : core.iter.traits.iterator.Iterator I T)
    (predInst : core.ops.function.FnMut P T Bool) (iter : I) (predicate : P) :
    Result (Option T × I) := do
  let (item, rest) ← iterInst.next iter
  match item with
  | none => ok (none, rest)
  | some value =>
    let (keep, predicate) ← predInst.call_mut predicate value
    if keep then ok (some value, rest)
    else core.iter.traits.iterator.Iterator.find.default iterInst predInst rest predicate
partial_fixpoint

@[rust_fun
  "core::iter::adapters::rev::{core::iter::traits::iterator::Iterator<core::iter::adapters::rev::Rev<@I>, @Clause0_Clause0_Item>}::find"]
def core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.find
    {I P T : Type _} (iterInst : core.iter.traits.double_ended.DoubleEndedIterator I T)
    (predInst : core.ops.function.FnMut P T Bool)
    (iter : core.iter.adapters.rev.Rev I) (predicate : P) :
    Result (Option T × core.iter.adapters.rev.Rev I) :=
  core.iter.traits.iterator.Iterator.find.default
    { next := Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next iterInst }
    predInst iter predicate

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def core.option.OptionShared0T.cloned {T : Type _} (cloneInst : core.clone.Clone T)
    (value : Option T) : Result (Option T) := do
  match value with
  | none => ok none
  | some x => let x ← cloneInst.clone x; ok (some x)

/-- Hash lookup abstracted as a finite search using the supplied borrow and equality.
    Rust's equality and hashing must obey the HashMap/Borrow consistency laws. -/
def std.collections.hash.map.containsKeyList {K Q : Type _}
    (borrow : resources.core.borrow.Borrow K Q) (eq : core.cmp.Eq Q)
    (key : Q) : List K → Result Bool
  | [] => ok false
  | head :: tail => do
    let borrowed ← borrow.borrow head
    let same ← eq.partialEqInst.eq borrowed key
    if same then ok true else containsKeyList borrow eq key tail

@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key"]
noncomputable def std.collections.hash.map.HashMap.contains_key
    {K V S A Q H : Type _} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (borrow : resources.core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q)
    (eqQ : core.cmp.Eq Q) (self : std.collections.hash.map.HashMap K V S A)
    (key : Q) : Result Bool :=
  std.collections.hash.map.containsKeyList borrow eqQ key self.keys.toList

/-- Find the stored key equal to the borrowed query. As with `contains_key`,
    equality and hashing must obey the HashMap/Borrow consistency laws. -/
def std.collections.hash.map.findKeyList {K Q : Type _}
    (borrow : resources.core.borrow.Borrow K Q) (eq : core.cmp.Eq Q)
    (key : Q) : List K → Result (Option K)
  | [] => ok none
  | head :: tail => do
    let borrowed ← borrow.borrow head
    let same ← eq.partialEqInst.eq key borrowed
    if same then ok (some head) else findKeyList borrow eq key tail

/-- Return the value stored under the matching borrowed key. Hashing and storage
    are abstracted away under the same assumptions as `contains_key`. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get"]
noncomputable def std.collections.hash.map.HashMap.get
    {K V S A Q H : Type _} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (borrow : resources.core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q)
    (eqQ : core.cmp.Eq Q) (self : std.collections.hash.map.HashMap K V S A)
    (key : Q) : Result (Option V) := by
  classical
  exact do
    let found ← std.collections.hash.map.findKeyList borrow eqQ key self.keys.toList
    match found with
    | none => ok none
    | some stored => ok (Finmap.lookup stored self)

/-- Remove the matching entry and return its previous value. Hashing and storage
    are abstracted away under the same assumptions as insertion and lookup. -/
@[rust_fun
  "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::remove"]
noncomputable def std.collections.hash.map.HashMap.remove
    {K V S A Q H : Type _} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (borrow : resources.core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q)
    (eqQ : core.cmp.Eq Q) (self : std.collections.hash.map.HashMap K V S A)
    (key : Q) : Result (Option V × std.collections.hash.map.HashMap K V S A) := by
  classical
  exact do
    let found ← std.collections.hash.map.findKeyList borrow eqQ key self.keys.toList
    match found with
    | none => ok (none, self)
    | some stored => ok (Finmap.lookup stored self, Finmap.erase stored self)

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::iter"]
def alloc.collections.btree.set.BTreeSet.iter {T A : Type _}
    (_allocator : resources.core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.Iter T) := ok self

@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Iter<'a, @T>, &'a @T>}::next"]
def alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    {T : Type _} : alloc.collections.btree.set.Iter T →
      Result (Option T × alloc.collections.btree.set.Iter T)
  | [] => ok (none, [])
  | x :: xs => ok (some x, xs)

@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::double_ended::DoubleEndedIterator<alloc::collections::btree::set::Iter<'a, @T>, &'_ @T>}::next_back"]
def alloc.collections.btree.set.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    {T : Type _} (self : alloc.collections.btree.set.Iter T) :
    Result (Option T × alloc.collections.btree.set.Iter T) :=
  match self.reverse with
  | [] => ok (none, [])
  | x :: xs => ok (some x, xs.reverse)

@[rust_fun "core::cmp::impls::{core::cmp::Ord<&'0 @A>}::cmp"]
def Shared0A.Insts.CoreCmpOrd.cmp {A : Type _} (ord : core.cmp.Ord A)
    (x y : A) : Result Ordering := ord.cmp x y

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<(core::ops::range::Bound<@T>, core::ops::range::Bound<@T>), @T>}::start_bound"]
def PairBoundBound.Insts.CoreOpsRangeRangeBounds.start_bound {T : Type _}
    (bounds : resources.core.ops.range.Bound T × resources.core.ops.range.Bound T) :
    Result (resources.core.ops.range.Bound T) := ok bounds.1

@[rust_fun
  "core::ops::range::{core::ops::range::RangeBounds<(core::ops::range::Bound<@T>, core::ops::range::Bound<@T>), @T>}::end_bound"]
def PairBoundBound.Insts.CoreOpsRangeRangeBounds.end_bound {T : Type _}
    (bounds : resources.core.ops.range.Bound T × resources.core.ops.range.Bound T) :
    Result (resources.core.ops.range.Bound T) := ok bounds.2

/-- Test one inclusive/exclusive search bound using the borrowed-key comparator. -/
def alloc.collections.btree.set.boundAllows {K : Type _} (ord : core.cmp.Ord K)
    (lower : Bool) (bound : resources.core.ops.range.Bound K) (key : K) : Result Bool := do
  match bound with
  | .Unbounded => ok true
  | .Included endpoint =>
    let o ← ord.cmp key endpoint
    ok (if lower then o != .lt else o != .gt)
  | .Excluded endpoint =>
    let o ← ord.cmp key endpoint
    ok (if lower then o == .gt else o == .lt)

/-- Preserve iteration order while retaining entries within both bounds. -/
def alloc.collections.btree.set.rangeList {T K : Type _}
    (borrow : resources.core.borrow.Borrow T K) (ord : core.cmp.Ord K)
    (lower upper : resources.core.ops.range.Bound K) : List T → Result (List T)
  | [] => ok []
  | x :: xs => do
    let key ← borrow.borrow x
    let lo ← alloc.collections.btree.set.boundAllows ord true lower key
    let hi ← alloc.collections.btree.set.boundAllows ord false upper key
    let rest ← rangeList borrow ord lower upper xs
    ok (if lo && hi then x :: rest else rest)

/-- Conservatively reject reversed bounds and equal exclusive bounds. The pinned
    library can skip these checks for an empty tree; that shortcut is not modeled. -/
def alloc.collections.btree.set.checkBounds {K : Type _} (ord : core.cmp.Ord K)
    (lower upper : resources.core.ops.range.Bound K) : Result Unit :=
  match lower, upper with
  | .Unbounded, _ | _, .Unbounded => ok ()
  | .Excluded lo, .Excluded hi => do
    let o ← ord.cmp lo hi
    if o = .lt then ok () else fail .panic
  | .Included lo, .Included hi | .Included lo, .Excluded hi | .Excluded lo, .Included hi => do
    let o ← ord.cmp lo hi
    if o = .gt then fail .panic else ok ()

/-- Logical bounded lookup. Borrowed and owned orderings must agree, as required
    by Rust's `BTreeSet` contract. The input and output are in comparator order. -/
@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::range"]
def alloc.collections.btree.set.BTreeSet.range {T A K R : Type _}
    (_allocator : resources.core.alloc.AllocatorClone A) (ord : core.cmp.Ord K)
    (borrow : resources.core.borrow.Borrow T K) (_ordT : core.cmp.Ord T)
    (bounds : resources.core.ops.range.RangeBounds R K)
    (self : alloc.collections.btree.set.BTreeSet T A) (query : R) :
    Result (alloc.collections.btree.set.Range T) := do
  let lower ← bounds.start_bound query
  let upper ← bounds.end_bound query
  alloc.collections.btree.set.checkBounds ord lower upper
  alloc.collections.btree.set.rangeList borrow ord lower upper self

/-- A sorted range iterator's minimum and maximum are its first and last elements. -/
@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Range<'a, @T>, &'a @T>}::min"]
def alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.min
    {T : Type _} (_ord : core.cmp.Ord T) (self : alloc.collections.btree.set.Range T) :
    Result (Option T) := ok self.head?

@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Range<'a, @T>, &'a @T>}::max"]
def alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.max
    {T : Type _} (_ord : core.cmp.Ord T) (self : alloc.collections.btree.set.Range T) :
    Result (Option T) := ok self.getLast?

/-- Opaque host result. The witness only inhabits the model; constructor proofs
    assume an explicit successful return and never rely on this witness's size.
    Correspondence to the host's `sysconf` call is an external assumption. -/
@[rust_fun "base::sys::unix::system_info::pagesize"]
opaque base.sys.unix.system_info.pagesize : Result Usize := ok 4096#usize

@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, alloc::alloc::Global>}::new"]
def alloc.collections.btree.map.BTreeMapKVGlobal.new (K V : Type _) :
    Result (alloc.collections.btree.map.BTreeMap K V alloc.alloc.Global) := ok ∅

/-- Locate the stored representative using borrowed keys and Rust's comparator.
    Tree shape and comparison order are abstracted away; borrowing and comparison
    are total, and borrowed and owned orderings agree under Rust's Ord contract. -/
def alloc.collections.btree.map.findEntryKey {K Q : Type _}
    (borrow : core.borrow.Borrow K Q) (ord : core.cmp.Ord Q)
    (key : Q) : List K → Result (Option K)
  | [] => ok none
  | head :: tail => do
    let borrowed ← borrow.borrow head
    let ordering ← ord.cmp key borrowed
    if ordering = .eq then ok (some head) else findEntryKey borrow ord key tail

/-- Key presence uses the same borrowed-key search as Rust's BTreeMap lookup. -/
@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::contains_key"]
noncomputable def alloc.collections.btree.map.BTreeMap.contains_key {K V A Q : Type _}
    (_alloc : core.alloc.AllocatorClone A) (borrow : core.borrow.Borrow K Q)
    (_ord : core.cmp.Ord K) (ordQ : core.cmp.Ord Q)
    (self : alloc.collections.btree.map.BTreeMap K V A) (key : Q) : Result Bool := do
  let found ← alloc.collections.btree.map.findEntryKey borrow ordQ key self.keys.toList
  ok found.isSome

/-- Write back only the value at the key captured by `entry`. Entry keys and variants
    cannot change through the modeled value borrows. A vacant entry dropped before
    insertion leaves the map unchanged. -/
noncomputable def alloc.collections.btree.map.entryBack {K V A : Type _}
    (self : alloc.collections.btree.map.BTreeMap K V A) (key : K)
    (entry : resources.alloc.collections.btree.map.entry.Entry K V A) :
    alloc.collections.btree.map.BTreeMap K V A := by
  classical
  exact match entry with
  | .Occupied e => Finmap.insert key e.value self
  | .Vacant e => match e.value with
    | none => self
    | some value => Finmap.insert key value self

@[rust_fun
  "alloc::collections::btree::map::{alloc::collections::btree::map::BTreeMap<@K, @V, @A>}::entry"]
noncomputable def alloc.collections.btree.map.BTreeMap.entry {K V A : Type _}
    (_alloc : core.alloc.AllocatorClone A) (ord : core.cmp.Ord K)
    (self : alloc.collections.btree.map.BTreeMap K V A) (key : K) :
    Result (resources.alloc.collections.btree.map.entry.Entry K V A ×
      (resources.alloc.collections.btree.map.entry.Entry K V A →
        alloc.collections.btree.map.BTreeMap K V A)) := by
  classical
  exact do
    let found ← alloc.collections.btree.map.findEntryKey
      ⟨core.borrow.Borrow.Blanket.borrow⟩ ord key self.keys.toList
    let storedKey := found.getD key
    let entry := match Finmap.lookup storedKey self with
      | none => .Vacant ⟨storedKey, none⟩
      | some value => .Occupied ⟨storedKey, value⟩
    ok (entry, alloc.collections.btree.map.entryBack self storedKey)

@[rust_fun
  "alloc::collections::btree::map::entry::{alloc::collections::btree::map::entry::OccupiedEntry<'a, @K, @V, @A>}::into_mut"]
def alloc.collections.btree.map.entry.OccupiedEntry.into_mut {K V A : Type _}
    (_ord : core.cmp.Ord K) (_alloc : core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.map.entry.OccupiedEntry K V A) :
    Result (V × (V → alloc.collections.btree.map.entry.OccupiedEntry K V A)) :=
  ok (self.value, fun value => { self with value := value })

@[rust_fun
  "alloc::collections::btree::map::entry::{alloc::collections::btree::map::entry::VacantEntry<'a, @K, @V, @A>}::insert"]
def alloc.collections.btree.map.entry.VacantEntry.insert {K V A : Type _}
    (_ord : core.cmp.Ord K) (_alloc : core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.map.entry.VacantEntry K V A) (value : V) :
    Result (V × (V → alloc.collections.btree.map.entry.VacantEntry K V A)) :=
  ok (value, fun value => { self with value := some value })

/-- Construct the lazy flat-map adapter without evaluating the closure. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::flat_map"]
def core.iter.traits.iterator.Iterator.flat_map.default {I U F T B J : Type _}
    (_iter : core.iter.traits.iterator.Iterator I T)
    (_into : core.iter.traits.collect.IntoIterator U B J)
    (_f : core.ops.function.FnMut F T U) (iter : I) (f : F) :
    Result (core.iter.adapters.flatten.FlatMap I U F B J) := ok ⟨some iter, f, none⟩

/-- Forward `FlatMap::next`, following `FlattenCompat::next`: drain the current
    inner iterator, skip empty inners, and fuse the outer iterator at its first
    `None`. Preserve closure state and propagate failures. This models standard
    library behavior; it is not a verification of the Rust iterator internals. -/
@[rust_fun
  "core::iter::adapters::flatten::{core::iter::traits::iterator::Iterator<core::iter::adapters::flatten::FlatMap<@I, @U, @F, @B, @J>, @B>}::next"]
def core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.next
    {I U F T B J : Type _} (iter : core.iter.traits.iterator.Iterator I T)
    (into : core.iter.traits.collect.IntoIterator U B J)
    (f : core.ops.function.FnMut F T U)
    (self : core.iter.adapters.flatten.FlatMap I U F B J) :
    Result (Option B × core.iter.adapters.flatten.FlatMap I U F B J) := do
  match self.inner with
  | some inner =>
    let (item, inner) ← into.iteratorInst.next inner
    match item with
    | some value => ok (some value, { self with inner := some inner })
    | none => next iter into f { self with inner := none }
  | none =>
    match self.outer with
    | none => ok (none, self)
    | some outer =>
      let (item, outer) ← iter.next outer
      match item with
      | none => ok (none, { self with outer := none })
      | some value =>
        let (items, f') ← f.call_mut self.f value
        let inner ← into.into_iter items
        next iter into f ⟨some outer, f', some inner⟩
partial_fixpoint
