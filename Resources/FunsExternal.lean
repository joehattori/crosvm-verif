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
