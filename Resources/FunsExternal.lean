-- External functions for [resources]
module
public import Aeneas
public import Resources.Types
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

/-- Cloning preserves string contents; storage allocation is abstracted away. -/
@[rust_fun "alloc::string::{core::clone::Clone<alloc::string::String>}::clone"]
def alloc.string.String.Insts.CoreCloneClone.clone (self : String) : Result String :=
  ok self

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
  {F : Type} (opsfunctionFnOnceFTupleOrderingInst : core.ops.function.FnOnce F
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
  {Idx : Type} (r : core.ops.range.RangeInclusive Idx) : Result Idx :=
  ok r.start

/-- [core::ops::range::{core::ops::range::RangeInclusive<Idx>}::end]:
    Source: '/rustc/library/core/src/ops/range.rs', lines 450:4-450:35
    Name pattern: [core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::end]
    Visibility: public -/
@[rust_fun "core::ops::range::{core::ops::range::RangeInclusive<@Idx>}::end"]
def core.ops.range.RangeInclusive.end
  {Idx : Type} (r : core.ops.range.RangeInclusive Idx) : Result Idx :=
  ok r.end

/-- Construct a lazy filter, preserving both the iterator and predicate state. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::filter"]
def core.iter.traits.iterator.Iterator.filter.default
  {I P T : Type} (_iterInst : core.iter.traits.iterator.Iterator I T)
  (_predInst : core.ops.function.FnMut P T Bool)
  (iter : I) (predicate : P) : Result (core.iter.adapters.filter.Filter I P) :=
  ok ⟨iter, predicate⟩

/-- Compatibility with the pinned backend's Iterator model, which lacks a
    filter field. Rust's default method constructs the adapter above.
    The constructor uses Vec::IntoIter, which uses this default. This bridge
    does not model an arbitrary iterator overriding `filter`. -/
def Aeneas.Std.core.iter.traits.iterator.Iterator.filter
  {I P T : Type} (iterInst : core.iter.traits.iterator.Iterator I T)
  (predInst : core.ops.function.FnMut P T Bool)
  (iter : I) (predicate : P) : Result (_root_.core.iter.adapters.filter.Filter I P) :=
  _root_.core.iter.traits.iterator.Iterator.filter.default iterInst predInst iter predicate

/-- Search until the next accepted element, keeping mutations of the predicate
    even when an element is rejected. Infinite rejection may diverge. -/
@[rust_fun
  "core::iter::adapters::filter::{core::iter::traits::iterator::Iterator<core::iter::adapters::filter::Filter<@I, @P>, @Clause0_Item>}::next"]
def core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next
  {I P T : Type} (iterInst : core.iter.traits.iterator.Iterator I T)
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
def std.collections.hash.map.HashMapKVRandomStateGlobal.new (K V : Type) :
  Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState Global) :=
  ok ∅

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, alloc::alloc::Global>}::new"]
def alloc.collections.btree.set.BTreeSetTGlobal.new (T : Type) :
  Result (alloc.collections.btree.set.BTreeSet T Global) :=
  ok []

/-- Insert in comparator order. An equal element retains the existing value,
    as in Rust's BTreeSet::insert (in contrast with replace). -/
def alloc.collections.btree.set.insertList {T : Type} (ord : core.cmp.Ord T)
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
  {T A : Type} (_allocator : resources.core.alloc.AllocatorClone A) (ord : core.cmp.Ord T)
  (self : alloc.collections.btree.set.BTreeSet T A) (value : T) :
  Result (Bool × alloc.collections.btree.set.BTreeSet T A) :=
  alloc.collections.btree.set.insertList ord value self

@[rust_fun "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow"]
def core.borrow.Borrow.Blanket.borrow {T : Type} (value : T) : Result T := ok value

/-- Remove the first comparator-equal borrowed key. On a valid BTreeSet there
    is at most one such element. Borrowed and owned orderings must agree. -/
def alloc.collections.btree.set.removeList {T Q : Type}
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
    {T A Q : Type} (_allocator : resources.core.alloc.AllocatorClone A)
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
    {K V S A H : Type} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (self : std.collections.hash.map.HashMap K V S A) (key : K) (value : V) :
    Result (Option V × std.collections.hash.map.HashMap K V S A) := by
  classical
  exact ok (Finmap.lookup key self, Finmap.insert key value self)

/- The following hash operations occur only in dictionaries passed to the
   abstract map. They deliberately fail rather than assert any hash behavior.
   No successful direct hash computation is modeled or verified. -/
def Isize.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : Isize) (_ : H) : Result H := fail .panic
def Usize.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : Usize) (_ : H) : Result H := fail .panic
def U8.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
    (_ : U8) (_ : H) : Result H := fail .panic
def U64.Insts.CoreHashHash.hash {H : Type} (_ : core.hash.Hasher H)
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
    {I P T : Type} (iterInst : core.iter.traits.iterator.Iterator I T)
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
    {I P T : Type} (iterInst : core.iter.traits.double_ended.DoubleEndedIterator I T)
    (predInst : core.ops.function.FnMut P T Bool)
    (iter : core.iter.adapters.rev.Rev I) (predicate : P) :
    Result (Option T × core.iter.adapters.rev.Rev I) :=
  core.iter.traits.iterator.Iterator.find.default
    { next := Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next iterInst }
    predInst iter predicate

@[rust_fun "core::option::{core::option::Option<&'0 @T>}::cloned"]
def core.option.OptionShared0T.cloned {T : Type} (cloneInst : core.clone.Clone T)
    (value : Option T) : Result (Option T) := do
  match value with
  | none => ok none
  | some x => let x ← cloneInst.clone x; ok (some x)

/-- Hash lookup abstracted as a finite search using the supplied borrow and equality.
    Rust's equality and hashing must obey the HashMap/Borrow consistency laws. -/
def std.collections.hash.map.containsKeyList {K Q : Type}
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
    {K V S A Q H : Type} (_eq : core.cmp.Eq K) (_hash : core.hash.Hash K)
    (_build : resources.core.hash.BuildHasher S H)
    (borrow : resources.core.borrow.Borrow K Q) (_hashQ : core.hash.Hash Q)
    (eqQ : core.cmp.Eq Q) (self : std.collections.hash.map.HashMap K V S A)
    (key : Q) : Result Bool :=
  std.collections.hash.map.containsKeyList borrow eqQ key self.keys.toList

@[rust_fun
  "alloc::collections::btree::set::{alloc::collections::btree::set::BTreeSet<@T, @A>}::iter"]
def alloc.collections.btree.set.BTreeSet.iter {T A : Type}
    (_allocator : resources.core.alloc.AllocatorClone A)
    (self : alloc.collections.btree.set.BTreeSet T A) :
    Result (alloc.collections.btree.set.Iter T) := ok self

@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::iterator::Iterator<alloc::collections::btree::set::Iter<'a, @T>, &'a @T>}::next"]
def alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.next
    {T : Type} : alloc.collections.btree.set.Iter T →
      Result (Option T × alloc.collections.btree.set.Iter T)
  | [] => ok (none, [])
  | x :: xs => ok (some x, xs)

@[rust_fun
  "alloc::collections::btree::set::{core::iter::traits::double_ended::DoubleEndedIterator<alloc::collections::btree::set::Iter<'a, @T>, &'_ @T>}::next_back"]
def alloc.collections.btree.set.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back
    {T : Type} (self : alloc.collections.btree.set.Iter T) :
    Result (Option T × alloc.collections.btree.set.Iter T) :=
  match self.reverse with
  | [] => ok (none, [])
  | x :: xs => ok (some x, xs.reverse)
