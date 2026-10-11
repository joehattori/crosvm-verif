module
public import Resources.AddressAllocatorCollections
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

/-- Addresses represented by a list of ranges. -/
def Covers (rs : List AddressRange) (addr : Nat) : Prop :=
  ∃ r ∈ rs, r.containsModel addr

/-- Initialization establishes the free-region invariant used by updates. -/
theorem initialState.validRegions {pool : AddressRange} {a : AddressAllocator}
    (h : initialState pool a) : ValidRegions a.regions := by
  rw [h.2.2.1]
  by_cases hn : pool.isEmptyModel <;> simp [initialPools, hn]

private theorem covers_split (rs rest : List AddressRange) (slot range before after : AddressRange)
    (hv : ValidRegions rs) (hslot : slot ∈ rs)
    (hsub : slot.start.val ≤ range.start.val ∧ range.end.val ≤ slot.end.val)
    (hcover : ∀ addr, (before.containsModel addr ∨ after.containsModel addr) ↔
      slot.containsModel addr ∧ ¬range.containsModel addr)
    (hmem : ∀ r, r ∈ rest ↔
      (r = after ∧ ¬after.isEmptyModel) ∨ (r = before ∧ ¬before.isEmptyModel) ∨
        r ∈ rs ∧ r ≠ slot) :
    ∀ addr, Covers rest addr ↔ Covers rs addr ∧ ¬range.containsModel addr := by
  intro addr
  constructor
  · rintro ⟨r, hr, ha⟩
    rcases (hmem r).mp hr with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨hr, hne⟩
    · have h := (hcover addr).mp (Or.inr ha)
      exact ⟨⟨slot, hslot, h.1⟩, h.2⟩
    · have h := (hcover addr).mp (Or.inl ha)
      exact ⟨⟨slot, hslot, h.1⟩, h.2⟩
    · refine ⟨⟨r, hr, ha⟩, ?_⟩
      have hd := hv.disjoint hr hslot hne
      simp only [DisjointRanges, AddressRange.containsModel] at *
      omega
  · rintro ⟨⟨r, hr, ha⟩, hn⟩
    by_cases he : r = slot
    · subst r
      rcases (hcover addr).mpr ⟨ha, hn⟩ with hb | ha
      · refine ⟨before, (hmem before).mpr (Or.inr (Or.inl ⟨rfl, ?_⟩)), hb⟩
        simp only [AddressRange.isEmptyModel, AddressRange.containsModel] at *
        omega
      · refine ⟨after, (hmem after).mpr (Or.inl ⟨rfl, ?_⟩), ha⟩
        simp only [AddressRange.isEmptyModel, AddressRange.containsModel] at *
        omega
    · exact ⟨r, (hmem r).mpr (Or.inr (Or.inr ⟨hr, he⟩)), ha⟩

/-- Allocate a nonempty subrange of an existing free slot. The helper preserves
    the free-region invariant, removes exactly the requested addresses, and
    updates exactly one map entry. It checks neither containment nor key freshness. -/
@[step]
theorem internal_allocate_from_slot_spec (self : AddressAllocator)
    (slot range : AddressRange) (allocation : resources.Alloc) (tag : String)
    (hv : ValidRegions self.regions) (hslot : slot ∈ self.regions)
    (hn : ¬range.isEmptyModel)
    (hsub : slot.start.val ≤ range.start.val ∧ range.end.val ≤ slot.end.val) :
    AddressAllocator.internal_allocate_from_slot self slot range allocation tag
      ⦃ result a => result = .Ok range.start ∧
        a.pools = self.pools ∧ a.min_align = self.min_align ∧
        a.preferred_align = self.preferred_align ∧
        a.allocs = Finmap.insert allocation (range, tag) self.allocs ∧
        ValidRegions a.regions ∧
        ∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∧ ¬range.containsModel addr ⦄ := by
  unfold AddressAllocator.internal_allocate_from_slot
  step with remove_region_spec self.regions slot hv hslot as ⟨removed, rs, hremoved, hvalid, hmem⟩
  simp only [hremoved]
  step
  step with AddressRange.non_overlapping_ranges_spec slot range
    as ⟨before, after, hcover, hdisjoint⟩
  have hbd : ¬before.isEmptyModel → ∀ r ∈ rs, DisjointRanges before r := by
    intro hb r hr
    have hd := hv.disjoint hslot ((hmem r).mp hr).1 (Ne.symm ((hmem r).mp hr).2)
    have hrn := hvalid.1 r hr
    have hc := hcover (max before.start.val r.start.val)
    simp only [DisjointRanges, AddressRange.containsModel, AddressRange.isEmptyModel] at *
    omega
  have had : ¬after.isEmptyModel → ∀ r ∈ rs, DisjointRanges after r := by
    intro ha r hr
    have hd := hv.disjoint hslot ((hmem r).mp hr).1 (Ne.symm ((hmem r).mp hr).2)
    have hrn := hvalid.1 r hr
    have hc := hcover (max after.start.val r.start.val)
    simp only [DisjointRanges, AddressRange.containsModel, AddressRange.isEmptyModel] at *
    omega
  have hba : ¬before.isEmptyModel → ¬after.isEmptyModel → DisjointRanges after before := by
    intro hb ha
    have hd := hdisjoint hn (max before.start.val after.start.val)
    simp only [DisjointRanges, AddressRange.containsModel, AddressRange.isEmptyModel] at *
    omega
  suffices h : (do
    let rs1 ← insertRemainder rs before
    let rs2 ← insertRemainder rs1 after
    let (_, hm) ← _root_.std.collections.hash.map.HashMap.insert
      resources.Alloc.Insts.CoreCmpEq resources.Alloc.Insts.CoreHashHash
      resources.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      self.allocs allocation (range, tag)
    ok (core.result.Result.Ok range.start, { self with allocs := hm, regions := rs2 })) ⦃ result a =>
      result = .Ok range.start ∧ a.pools = self.pools ∧ a.min_align = self.min_align ∧
      a.preferred_align = self.preferred_align ∧
      a.allocs = Finmap.insert allocation (range, tag) self.allocs ∧
      ValidRegions a.regions ∧ ∀ addr, Covers a.regions addr ↔
        Covers self.regions addr ∧ ¬range.containsModel addr ⦄ by
    simpa only [insertRemainder, Aeneas.Std.bind_assoc] using h
  step with insertRemainder_spec rs before hvalid hbd as ⟨rs1, hv1, hm1⟩
  have had1 : ¬after.isEmptyModel → ∀ r ∈ rs1, DisjointRanges after r := by
    intro ha r hr
    rcases (hm1 r).mp hr with ⟨rfl, hb⟩ | hr
    · exact hba hb ha
    · exact had ha r hr
  step with insertRemainder_spec rs1 after hv1 had1 as ⟨rs2, hv2, hm2⟩
  simp [_root_.std.collections.hash.map.HashMap.insert, bind_ok]
  refine ⟨hv2, ?_⟩
  have hc : ∀ addr, (before.containsModel addr ∨ after.containsModel addr) ↔
      slot.containsModel addr ∧ ¬range.containsModel addr := by
    simpa only [AddressRange.containsModel, and_assoc] using hcover
  have hm : ∀ r, r ∈ rs2 ↔
      (r = after ∧ ¬after.isEmptyModel) ∨ (r = before ∧ ¬before.isEmptyModel) ∨
        r ∈ self.regions ∧ r ≠ slot := by
    intro r
    simp only [hm2, hm1, hmem]
  simpa [AddressRange.containsModel] using
    covers_split self.regions rs2 slot range before after hv hslot hsub hc hm

end resources.address_allocator.AddressAllocator
