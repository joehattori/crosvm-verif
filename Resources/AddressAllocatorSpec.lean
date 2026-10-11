module
public import Resources.AddressRangeSpec
-- The pinned library does not export the unfolding equation for iterToList.
import all Aeneas.Std.VecIter
@[expose] public section
open Aeneas Aeneas.Std Result
open resources.address_range resources.address_allocator

namespace resources.address_allocator.AddressAllocator

/-- Initial pools omit an empty input range. -/
abbrev initialPools (pool : AddressRange) : List AddressRange :=
  if pool.isEmptyModel then [] else [pool]

/-- A new allocator has no allocations and all of its pool is free. -/
def initialState (pool : AddressRange) (a : AddressAllocator) : Prop :=
  a.pools.val = initialPools pool ∧
  a.allocs = ∅ ∧ a.regions = initialPools pool ∧
  a.min_align = 4#u64 ∧ a.preferred_align = 4#u64

private abbrev poolIterator :=
  core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator
    (core.iter.traits.iterator.IteratorVecIntoIter AddressRange)
    (new_from_list.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressRangeBool
      (core.iter.traits.collect.IntoIteratorVec AddressRange))

private abbrev filterState (pools : List AddressRange) (h : pools.length ≤ Usize.max) :
    _root_.core.iter.adapters.filter.Filter (alloc.vec.into_iter.IntoIter AddressRange) Unit :=
  ⟨alloc.vec.Vec.from pools h, ()⟩

private theorem filter_next_empty :
    poolIterator.next (filterState [] (by simp)) =
      ok (none, filterState [] (by simp)) := by
  change _root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next _ _ _ = _
  rw [_root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next.eq_def]
  change (ok (none, (alloc.vec.Vec.from [] (by simp) : alloc.vec.into_iter.IntoIter AddressRange)) >>= _) = _
  erw [bind_tc_ok]
  rfl

private theorem filter_next_singleton (pool : AddressRange) (h) :
    poolIterator.next (filterState [pool] h) =
      ok ((if pool.isEmptyModel then none else some pool), filterState [] (by simp)) := by
  change _root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next _ _ _ = _
  rw [_root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next.eq_def]
  change (ok (some pool, (alloc.vec.Vec.from [] (by simp) : alloc.vec.into_iter.IntoIter AddressRange)) >>= _) = _
  erw [bind_tc_ok]
  change (do
    let (keep, predicate) ← new_from_list.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressRangeBool.call_mut
      (core.iter.traits.collect.IntoIteratorVec AddressRange) () pool
    if keep then ok (some pool, filterState [] (by simp))
    else poolIterator.next (filterState [] (by simp))) = _
  rw [filter_next_empty]
  simp [new_from_list.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressRangeBool.call_mut,
    AddressRange.is_empty, AddressRange.isEmptyModel]
  split <;> simp_all

private theorem collect_empty (acc : List AddressRange) :
    alloc.vec.FromIteratorVec.iterToList poolIterator (filterState [] (by simp)) acc =
      ok acc.reverse := by
  rw [alloc.vec.FromIteratorVec.iterToList.eq_def, filter_next_empty]
  erw [bind_tc_ok]

private theorem collect_singleton (pool : AddressRange) (h) :
    alloc.vec.FromIteratorVec.iterToList poolIterator (filterState [pool] h) [] =
      ok (initialPools pool) := by
  rw [alloc.vec.FromIteratorVec.iterToList.eq_def, filter_next_singleton]
  by_cases he : pool.isEmptyModel
  · simp [he, initialPools]
  · simp [he, collect_empty, initialPools]

/-- With default alignments, construction succeeds even for an empty pool
    and establishes the exact initial state. -/
@[step]
theorem new_default_spec (pool : AddressRange) :
    AddressAllocator.new pool none none ⦃ result =>
      ∃ a, result = .Ok a ∧ initialState pool a ⦄ := by
  unfold AddressAllocator.new AddressAllocator.new_from_list
  simp only [alloc.vec.IntoIteratorVec.into_iter,
    Aeneas.Std.core.iter.traits.iterator.Iterator.filter,
    _root_.core.iter.traits.iterator.Iterator.filter.default,
    core.iter.traits.iterator.Iterator.collect.default,
    alloc.vec.FromIteratorVec.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter]
  simp [Array.to_slice, alloc.slice.Slice.into_vec, Array.make,
    core.option.Option.unwrap_or, lift,
    core.num.U64.is_power_of_two, UScalar.is_power_of_two,
    show Nat.isPowerOfTwo 4 from by decide]
  erw [collect_singleton]
  have hlen : (initialPools pool).length ≤ Usize.max := by
    unfold initialPools
    split <;> simp
    scalar_tac
  simp [hlen, _root_.alloc.collections.btree.set.BTreeSetTGlobal.new,
    core.slice.Slice.iter, alloc.vec.Vec.deref,
    _root_.std.collections.hash.map.HashMapKVRandomStateGlobal.new]
  unfold new_from_list_loop
  by_cases h : pool.isEmptyModel
  all_goals
    simp [initialPools, h]
    rw [loop.eq_def]
    simp [new_from_list_loop.body, core.slice.iter.IteratorSliceIter.next,
      _root_.alloc.collections.btree.set.BTreeSet.insert,
      _root_.alloc.collections.btree.set.insertList,
      initialState, initialPools, h]
  rw [loop.eq_def]
  simp
  rfl

end resources.address_allocator.AddressAllocator
