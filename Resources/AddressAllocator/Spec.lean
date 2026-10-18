module
public import Resources.AddressAllocator.Collections
-- The pinned library does not export the unfolding equation for iterToList.
import all Aeneas.Std.VecIter
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std Result
open resources.address_range resources.address_allocator

namespace resources.address_allocator.AddressAllocator

/-- Addresses represented by a list of ranges. -/
def Covers (rs : List AddressRange) (addr : Nat) : Prop :=
  ∃ r ∈ rs, r.containsModel addr

/-- Addresses recorded in the allocation map. -/
def Allocated (a : AddressAllocator) (addr : Nat) : Prop :=
  ∃ allocation range tag, Finmap.lookup allocation a.allocs = some (range, tag) ∧
    range.containsModel addr

/-- Free-region and alignment properties, also valid during internal updates. -/
structure StructuralInvariant (a : AddressAllocator) : Prop where
  validRegions : ValidRegions a.regions
  minAlign : a.min_align.val.isPowerOfTwo
  preferredAlign : a.preferred_align.val.isPowerOfTwo
  alignOrder : a.min_align.val ≤ a.preferred_align.val

/-- The recorded pools are partitioned into free addresses and disjoint allocations. -/
structure WellFormed (a : AddressAllocator) : Prop extends StructuralInvariant a where
  accounting : ∀ addr, Covers a.pools.val addr ↔ Covers a.regions addr ∨ Allocated a addr
  freeDisjoint : ∀ allocation range tag, Finmap.lookup allocation a.allocs = some (range, tag) →
    ∀ addr, Covers a.regions addr → ¬range.containsModel addr
  allocsDisjoint : ∀ key range tag, Finmap.lookup key a.allocs = some (range, tag) →
    ∀ key' range' tag', Finmap.lookup key' a.allocs = some (range', tag') → key ≠ key' →
      ∀ addr, range.containsModel addr → ¬range'.containsModel addr

theorem WellFormed.free_mem_pools {a : AddressAllocator} (h : WellFormed a)
    {addr : Nat} (ha : Covers a.regions addr) : Covers a.pools.val addr :=
  (h.accounting addr).mpr (Or.inl ha)

theorem WellFormed.allocated_mem_pools {a : AddressAllocator} (h : WellFormed a)
    {addr : Nat} (ha : Allocated a addr) : Covers a.pools.val addr :=
  (h.accounting addr).mpr (Or.inr ha)

private theorem wellFormed_empty_allocs {a : AddressAllocator}
    (hs : StructuralInvariant a) (he : a.allocs = ∅)
    (hc : ∀ addr, Covers a.pools.val addr ↔ Covers a.regions addr) : WellFormed a := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · simpa [Allocated, he] using hc
  · simp [he]
  · simp [he]

private theorem allocated_insert_iff {self a : AddressAllocator} {allocation : resources.Alloc}
    {range : AddressRange} {tag : String}
    (hfresh : allocation ∉ self.allocs)
    (hm : a.allocs = Finmap.insert allocation (range, tag) self.allocs) (addr : Nat) :
    Allocated a addr ↔ range.containsModel addr ∨ Allocated self addr := by
  have hnone := Finmap.lookup_eq_none.mpr hfresh
  constructor
  · rintro ⟨key, r, label, hlookup, ha⟩
    rw [hm] at hlookup
    by_cases he : key = allocation
    · subst key
      simp only [Finmap.lookup_insert, Option.some.injEq, Prod.mk.injEq] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      exact Or.inl ha
    · rw [Finmap.lookup_insert_of_ne _ he] at hlookup
      exact Or.inr ⟨key, r, label, hlookup, ha⟩
  · rintro (ha | ⟨key, r, label, hlookup, ha⟩)
    · exact ⟨allocation, range, tag, by simp [hm], ha⟩
    · have he : key ≠ allocation := by rintro rfl; simp_all
      exact ⟨key, r, label, by simpa [hm, Finmap.lookup_insert_of_ne _ he] using hlookup, ha⟩

/-- Moving a free range into a fresh allocation preserves the full partition. -/
private theorem WellFormed.allocate {self a : AddressAllocator} {allocation : resources.Alloc}
    {range : AddressRange} {tag : String} (h : WellFormed self) (hs : StructuralInvariant a)
    (hfresh : allocation ∉ self.allocs) (hp : a.pools = self.pools)
    (hm : a.allocs = Finmap.insert allocation (range, tag) self.allocs)
    (havailable : ∀ addr, range.containsModel addr → Covers self.regions addr)
    (hc : ∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∧ ¬range.containsModel addr) :
    WellFormed a := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro addr
    rw [hp, h.accounting, hc, allocated_insert_iff hfresh hm]
    have := havailable addr
    tauto
  · intro key r label hlookup addr hfree ha
    rw [hm] at hlookup
    by_cases he : key = allocation
    · subst key
      simp only [Finmap.lookup_insert, Option.some.injEq, Prod.mk.injEq] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      exact ((hc addr).mp hfree).2 ha
    · rw [Finmap.lookup_insert_of_ne _ he] at hlookup
      exact h.freeDisjoint key r label hlookup addr ((hc addr).mp hfree).1 ha
  · intro key r label hlookup key' r' label' hlookup' hne addr ha ha'
    rw [hm] at hlookup hlookup'
    by_cases he : key = allocation
    · subst key
      simp only [Finmap.lookup_insert, Option.some.injEq, Prod.mk.injEq] at hlookup
      rcases hlookup with ⟨rfl, rfl⟩
      rw [Finmap.lookup_insert_of_ne _ hne.symm] at hlookup'
      exact h.freeDisjoint key' r' label' hlookup' addr (havailable addr ha) ha'
    · rw [Finmap.lookup_insert_of_ne _ he] at hlookup
      by_cases he' : key' = allocation
      · subst key'
        simp only [Finmap.lookup_insert, Option.some.injEq, Prod.mk.injEq] at hlookup'
        rcases hlookup' with ⟨rfl, rfl⟩
        exact h.freeDisjoint key r label hlookup addr (havailable addr ha') ha
      · rw [Finmap.lookup_insert_of_ne _ he'] at hlookup'
        exact h.allocsDisjoint key r label hlookup key' r' label' hlookup' hne addr ha ha'

private theorem lookup_of_erase {self a : AddressAllocator} {allocation key : resources.Alloc}
    {range : AddressRange} {tag : String} (hm : a.allocs = Finmap.erase allocation self.allocs)
    (hl : Finmap.lookup key a.allocs = some (range, tag)) :
    key ≠ allocation ∧ Finmap.lookup key self.allocs = some (range, tag) := by
  rw [hm] at hl
  by_cases he : key = allocation
  · subst key; simp at hl
  · exact ⟨he, by simpa only [Finmap.lookup_erase_ne he] using hl⟩

/-- Returning a recorded range to free space preserves the full partition. -/
private theorem WellFormed.release {self a : AddressAllocator} {allocation : resources.Alloc}
    {range : AddressRange} {tag : String} (h : WellFormed self) (hs : StructuralInvariant a)
    (hl : Finmap.lookup allocation self.allocs = some (range, tag))
    (hp : a.pools = self.pools) (hm : a.allocs = Finmap.erase allocation self.allocs)
    (hc : ∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∨ range.containsModel addr) :
    WellFormed a := by
  refine ⟨hs, ?_, ?_, ?_⟩
  · intro addr
    rw [hp, h.accounting, hc]
    constructor
    · rintro (hf | ⟨key, r, label, hlookup, ha⟩)
      · exact Or.inl (Or.inl hf)
      · by_cases he : key = allocation
        · subst key
          rw [hl] at hlookup
          cases hlookup
          exact Or.inl (Or.inr ha)
        · exact Or.inr ⟨key, r, label, by simpa [hm, Finmap.lookup_erase_ne he] using hlookup, ha⟩
    · rintro ((hf | ha) | ⟨key, r, label, hlookup, ha⟩)
      · exact Or.inl hf
      · exact Or.inr ⟨allocation, range, tag, hl, ha⟩
      · exact Or.inr ⟨key, r, label, (lookup_of_erase hm hlookup).2, ha⟩
  · intro key r label hlookup addr hfree ha
    obtain ⟨hne, hlookup⟩ := lookup_of_erase hm hlookup
    rcases (hc addr).mp hfree with hf | hr
    · exact h.freeDisjoint key r label hlookup addr hf ha
    · exact h.allocsDisjoint allocation range tag hl key r label hlookup hne.symm addr hr ha
  · intro key r label hlookup key' r' label' hlookup' hne addr ha ha'
    exact h.allocsDisjoint key r label (lookup_of_erase hm hlookup).2
      key' r' label' (lookup_of_erase hm hlookup').2 hne addr ha ha'

/-! ### Construction and slot allocation -/

/-- Errors shared by `new` and `new_from_list`, after resolving the alignment
    defaults. Empty pools are allowed; constructor errors depend only on alignment. -/
def newError (min_align preferred_align : Option U64) : Option resources.Error :=
  let minimum := min_align.getD 4#u64
  let preferred := preferred_align.getD minimum
  if minimum.val.isPowerOfTwo ∧ preferred.val.isPowerOfTwo ∧ minimum.val ≤ preferred.val
  then none else some .BadAlignment

/-- Initial pools omit an empty input range. -/
abbrev initialPools (pool : AddressRange) : List AddressRange :=
  if pool.isEmptyModel then [] else [pool]

/-- A new allocator has no allocations and all of its pool is free. -/
def initialState (pool : AddressRange) (a : AddressAllocator)
    (min_align : U64 := 4#u64) (preferred_align : U64 := min_align) : Prop :=
  a.pools.val = initialPools pool ∧
  a.allocs = ∅ ∧ a.regions = initialPools pool ∧
  a.min_align = min_align ∧ a.preferred_align = preferred_align

/-- Initialization establishes the free-region invariant used by updates. -/
theorem initialState.validRegions {pool : AddressRange} {a : AddressAllocator}
    {min_align preferred_align : U64} (h : initialState pool a min_align preferred_align) :
    ValidRegions a.regions := by
  rw [h.2.2.1]
  by_cases hn : pool.isEmptyModel <;> simp [initialPools, hn]

/-- A valid initial alignment configuration establishes the full invariant. -/
theorem initialState.wellFormed {pool : AddressRange} {a : AddressAllocator}
    {min_align preferred_align : U64} (h : initialState pool a min_align preferred_align)
    (hmin : min_align.val.isPowerOfTwo) (hpref : preferred_align.val.isPowerOfTwo)
    (horder : min_align.val ≤ preferred_align.val) : WellFormed a := by
  have hv := h.validRegions
  rcases h with ⟨hpools, hallocs, hmem, hminimum, hpreferred⟩
  apply wellFormed_empty_allocs
    ⟨hv, by simpa [hminimum] using hmin, by simpa [hpreferred] using hpref,
      by simpa [hminimum, hpreferred] using horder⟩ hallocs
  simp only [hpools, hmem, implies_true]

/-- Distinct nonempty input pools do not overlap; order and duplicates are unrestricted. -/
def DisjointPools (pools : List AddressRange) : Prop :=
  ∀ r ∈ pools, ∀ s ∈ pools, ¬r.isEmptyModel → ¬s.isEmptyModel →
    r ≠ s → DisjointRanges r s

/-- Construction preserves the nonempty input pools in their original order. -/
abbrev nonemptyPools (pools : List AddressRange) : List AddressRange :=
  pools.filter (fun r => decide (¬r.isEmptyModel))

/-- The pool vector preserves order and duplicates; the free set contains exactly
    the nonempty input ranges. There are no recorded allocations. -/
def initialStateFromList (pools : List AddressRange) (a : AddressAllocator)
    (min_align : U64 := 4#u64) (preferred_align : U64 := min_align) : Prop :=
  a.pools.val = nonemptyPools pools ∧ a.allocs = ∅ ∧
  (∀ r, r ∈ a.regions ↔ r ∈ nonemptyPools pools) ∧
  a.min_align = min_align ∧ a.preferred_align = preferred_align

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

private theorem filter_next_cons (pool : AddressRange) (pools : List AddressRange)
    (h : (pool :: pools).length ≤ Usize.max) :
    poolIterator.next (filterState (pool :: pools) h) =
      if pool.isEmptyModel then
        poolIterator.next (filterState pools (Nat.le_trans (Nat.le_succ _) h))
      else ok (some pool, filterState pools (Nat.le_trans (Nat.le_succ _) h)) := by
  change _root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next _ _ _ = _
  rw [_root_.core.iter.adapters.filter.Filter.Insts.CoreIterTraitsIteratorIterator.next.eq_def]
  have hnext : (core.iter.traits.iterator.IteratorVecIntoIter AddressRange).next
      (filterState (pool :: pools) h).iter =
      ok (some pool, (alloc.vec.Vec.from pools (Nat.le_trans (Nat.le_succ _) h) :
        alloc.vec.into_iter.IntoIter AddressRange)) := by
    simp only
    unfold alloc.vec.into_iter.IteratorIntoIter.next
    split
    · rename_i he
      change (alloc.vec.Vec.from (pool :: pools) h).val = [] at he
      simp at he
    · rename_i head tail he
      change (alloc.vec.Vec.from (pool :: pools) h).val = head :: tail at he
      simp only [alloc.vec.Vec.from_val, List.cons.injEq] at he
      rcases he with ⟨rfl, rfl⟩
      rfl
  rw [hnext]
  erw [bind_ok]
  change (do
    let (keep, _) ← new_from_list.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressRangeBool.call_mut
      (core.iter.traits.collect.IntoIteratorVec AddressRange) () pool
    if keep then ok (some pool, filterState pools (Nat.le_trans (Nat.le_succ _) h))
    else poolIterator.next (filterState pools (Nat.le_trans (Nat.le_succ _) h))) = _
  simp [new_from_list.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressRangeBool.call_mut,
    AddressRange.is_empty, AddressRange.isEmptyModel]
  split <;> simp_all [filterState]

private theorem collect_pools (pools : List AddressRange)
    (h : pools.length ≤ Usize.max) (acc : List AddressRange) :
    alloc.vec.FromIteratorVec.iterToList poolIterator (filterState pools h) acc =
      ok (acc.reverse ++ nonemptyPools pools) := by
  induction pools generalizing acc with
  | nil =>
    rw [alloc.vec.FromIteratorVec.iterToList.eq_def, filter_next_empty]
    simp [nonemptyPools]
  | cons pool pools ih =>
    rw [alloc.vec.FromIteratorVec.iterToList.eq_def, filter_next_cons]
    by_cases he : pool.isEmptyModel
    · simp only [he, ↓reduceIte]
      have htail := ih (by simp_all; omega) acc
      rw [alloc.vec.FromIteratorVec.iterToList.eq_def] at htail
      simpa [nonemptyPools, he] using htail
    · simp only [he, ↓reduceIte, bind_tc_ok]
      rw [ih]
      simp [nonemptyPools, List.filter_cons, AddressRange.isEmptyModel,
        List.reverse_cons, List.append_assoc] at he ⊢
      simp_all

private theorem initial_regions_loop_spec (pools : Slice AddressRange) (i : Nat)
    (rs : List AddressRange) (hi : i ≤ pools.val.length)
    (hn : ∀ r ∈ pools.val, ¬r.isEmptyModel) (hd : DisjointPools pools.val)
    (hv : ValidRegions rs) (hm : ∀ r, r ∈ rs ↔ r ∈ pools.val.take i) :
    new_from_list_loop ⟨pools, i⟩ rs ⦃ regions =>
      ValidRegions regions ∧ ∀ r, r ∈ regions ↔ r ∈ pools.val ⦄ := by
  unfold new_from_list_loop
  rw [loop.eq_def]
  simp only [new_from_list_loop.body, core.slice.iter.IteratorSliceIter.next,
    Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp
    have hpool : pools.val[i] ∈ pools.val := List.getElem_mem hnext
    step with insert_region_or_existing_spec rs pools.val[i] hv (hn _ hpool)
      (fun r hr hne => hd _ hpool r (List.mem_of_mem_take ((hm r).mp hr))
        (hn _ hpool) (hv.1 r hr) hne) as ⟨pair, hvalid, hmem⟩
    rcases pair with ⟨added, rest⟩
    simp
    have hmem' : ∀ r, r ∈ rest ↔ r ∈ pools.val.take (i + 1) := by
      intro r
      simp only [hmem, hm, List.take_succ_eq_append_getElem hnext, List.mem_append,
        List.mem_singleton, or_comm]
    exact initial_regions_loop_spec pools (i + 1) rest (by omega) hn hd hvalid hmem'
  · rename_i hdone
    simp
    exact ⟨hv, by simpa [List.take_of_length_le (by omega : pools.val.length ≤ i)] using hm⟩
termination_by pools.val.length - i

/-- Construct from a finite vector of pools in any order, allowing empty pools and
    duplicates. Distinct nonempty pools must be disjoint to establish well-formedness.
    `newError` characterizes the errors exactly. -/
@[step]
theorem new_from_list_spec (pools : alloc.vec.Vec AddressRange)
    (min_align preferred_align : Option U64) (hd : DisjointPools pools.val) :
    AddressAllocator.new_from_list (core.iter.traits.collect.IntoIteratorVec AddressRange)
      pools min_align preferred_align ⦃ result =>
      let minimum := min_align.getD 4#u64
      let preferred := preferred_align.getD minimum
      match newError min_align preferred_align with
      | some error => result = .Err error
      | none => ∃ a, result = .Ok a ∧
          initialStateFromList pools.val a minimum preferred ∧ WellFormed a ⦄ := by
  have hunwrap (x : Option U64) (d : U64) : core.option.Option.unwrap_or x d = x.getD d := by
    cases x <;> rfl
  have hcollect : alloc.vec.FromIteratorVec.iterToList poolIterator ⟨pools, ()⟩ [] =
      ok (nonemptyPools pools.val) := by
    simpa only [filterState, alloc.vec.Vec.val_from, List.reverse_nil, List.nil_append]
      using collect_pools pools.val pools.property []
  have hlen : (nonemptyPools pools.val).length ≤ Usize.max :=
    le_trans (List.length_filter_le _ _) pools.property
  have hd' : DisjointPools (nonemptyPools pools.val) := by
    intro r hr s hs
    exact hd r (List.mem_of_mem_filter hr) s (List.mem_of_mem_filter hs)
  unfold AddressAllocator.new_from_list newError
  simp only [alloc.vec.IntoIteratorVec.into_iter,
    Aeneas.Std.core.iter.traits.iterator.Iterator.filter,
    _root_.core.iter.traits.iterator.Iterator.filter.default,
    core.iter.traits.iterator.Iterator.collect.default,
    alloc.vec.FromIteratorVec.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter]
  simp [hunwrap, lift, core.num.U64.is_power_of_two, UScalar.is_power_of_two]
  erw [hcollect]
  simp [hlen, _root_.alloc.collections.btree.set.BTreeSetTGlobal.new,
    core.slice.Slice.iter, alloc.vec.Vec.deref,
    _root_.std.collections.hash.map.HashMapKVRandomStateGlobal.new]
  generalize hminimum : min_align.getD 4#u64 = minimum
  generalize hpreferred : preferred_align.getD minimum = preferred
  split
  · rename_i hmin
    have hpos := Nat.pos_of_isPowerOfTwo hmin
    split
    · scalar_tac
    · split
      · rename_i hpref
        split
        · rename_i horder
          simp_all [Nat.not_le.mpr horder]
        · rename_i horder
          step with initial_regions_loop_spec (Slice.from (nonemptyPools pools.val) hlen) 0 []
            (by simp) (by simp [nonemptyPools]) (by simpa using hd') (by simp) (by simp)
            as ⟨regions, hvalid, hmem⟩
          simp only [Slice.from_val] at hmem
          simp only [hmin, hpref, Nat.le_of_not_gt horder, and_self, ↓reduceIte]
          refine ⟨_, rfl, ?_, ?_⟩
          · simp [initialStateFromList, hmem]
          · apply wellFormed_empty_allocs ⟨hvalid, hmin, hpref, Nat.le_of_not_gt horder⟩ rfl
            intro addr
            simp only [Covers, alloc.vec.Vec.from_val]
            simp_rw [hmem]
      · simp_all
  · simp_all

private theorem initialStateFromList_singleton {pool : AddressRange} {a : AddressAllocator}
    {minimum preferred : U64} (h : initialStateFromList [pool] a minimum preferred)
    (hv : ValidRegions a.regions) : initialState pool a minimum preferred := by
  rcases h with ⟨hpools, hallocs, hmem, hmin, hpref⟩
  have hp : nonemptyPools [pool] = initialPools pool := by
    by_cases he : pool.isEmptyModel <;>
      simp_all [nonemptyPools, initialPools, List.filter_cons, AddressRange.isEmptyModel]
  rw [hp] at hpools hmem
  refine ⟨hpools, hallocs, ?_, hmin, hpref⟩
  by_cases he : pool.isEmptyModel
  · simp only [initialPools, he, ↓reduceIte, List.not_mem_nil, iff_false] at hmem ⊢
    exact List.eq_nil_iff_forall_not_mem.mpr hmem
  · simp only [initialPools, he, ↓reduceIte, List.mem_singleton] at hmem ⊢
    cases hr : a.regions with
    | nil => simpa [hr] using (hmem pool).mpr rfl
    | cons head tail =>
      have hh : head = pool := (hmem head).mp (by simp [hr])
      subst head
      have hsep := ((validRegions_cons _ _).mp (hr ▸ hv)).2.2
      have ht : tail = [] := by
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro r hm
        have heq : r = pool := (hmem r).mp (by simp [hr, hm])
        subst r
        have := hsep pool hm
        simp only [AddressRange.isEmptyModel] at he
        omega
      simp [ht]

/-- Construction establishes well-formedness and the exact initial state, including
    custom alignments. `newError` characterizes the errors exactly. -/
@[step]
theorem new_spec (pool : AddressRange) (min_align preferred_align : Option U64) :
    AddressAllocator.new pool min_align preferred_align ⦃ result =>
      let minimum := min_align.getD 4#u64
      let preferred := preferred_align.getD minimum
      match newError min_align preferred_align with
      | some error => result = .Err error
      | none => ∃ a, result = .Ok a ∧
          initialState pool a minimum preferred ∧ WellFormed a ⦄ := by
  unfold AddressAllocator.new
  simp [Array.to_slice, Array.make, alloc.slice.Slice.into_vec, lift]
  have hnew := new_from_list_spec (alloc.vec.Vec.from [pool] (by scalar_tac))
    min_align preferred_align (by simp [DisjointPools])
  simp only [alloc.vec.Vec.from] at hnew
  step with hnew as ⟨result, hresult⟩
  cases he : newError min_align preferred_align with
  | some error => simpa [he] using hresult
  | none =>
    simp only [he] at hresult ⊢
    obtain ⟨a, rfl, hs, hw⟩ := hresult
    exact ⟨a, rfl, initialStateFromList_singleton
      (by simpa [alloc.vec.Vec.val] using hs) hw.validRegions, hw⟩

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
    have hd := hdisjoint (max before.start.val after.start.val)
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

/-! ### Alignment arithmetic and fit predicates -/

/-- Round down to an alignment boundary, using unbounded arithmetic. -/
def alignDown (addr alignment : Nat) : Nat := addr - addr % alignment

/-- Round up to an alignment boundary, using unbounded arithmetic. -/
def alignUp (addr alignment : Nat) : Nat :=
  if addr % alignment = 0 then addr else addr + (alignment - addr % alignment)

theorem alignDown_eq (x a : Nat) : alignDown x a = a * (x / a) := by
  have := Nat.mod_add_div x a
  unfold alignDown
  omega

theorem alignDown_le (x a : Nat) : alignDown x a ≤ x := Nat.sub_le _ _

theorem alignDown_mod (x a : Nat) : alignDown x a % a = 0 := by
  rw [alignDown_eq]
  simp

theorem le_alignDown {x a y : Nat} (hy : y % a = 0) (h : y ≤ x) :
    y ≤ alignDown x a := by
  rw [alignDown_eq]
  have hdiv := Nat.div_le_div_right h (c := a)
  have hmul := Nat.mul_le_mul_left a hdiv
  have := Nat.mod_add_div y a
  omega

theorem alignUp_eq {x a : Nat} (ha : 0 < a) (h : x % a ≠ 0) :
    alignUp x a = a * (x / a + 1) := by
  have hr := Nat.mod_le x a
  have := Nat.mod_add_div x a
  have := Nat.mod_lt x ha
  simp only [alignUp, h, ↓reduceIte, Nat.mul_add, Nat.mul_one]
  omega

theorem le_alignUp (x a : Nat) : x ≤ alignUp x a := by
  unfold alignUp
  split <;> omega

theorem alignUp_mod (x a : Nat) (ha : 0 < a) : alignUp x a % a = 0 := by
  by_cases h : x % a = 0
  · simp [alignUp, h]
  · rw [alignUp_eq ha h]
    simp

theorem alignUp_le {x a y : Nat} (ha : 0 < a) (hy : y % a = 0) (h : x ≤ y) :
    alignUp x a ≤ y := by
  by_cases hr : x % a = 0
  · simpa [alignUp, hr] using h
  rw [alignUp_eq ha hr]
  have hx := Nat.mod_add_div x a
  have hyy := Nat.mod_add_div y a
  have hq : x / a + 1 ≤ y / a := by
    by_contra hn
    have hm := Nat.mul_le_mul_left a (show y / a ≤ x / a by omega)
    omega
  have hm := Nat.mul_le_mul_left a hq
  omega

/-- Clearing the low bits of a power-of-two alignment is mathematical rounding down. -/
theorem mask_alignDown (x alignment mask : U64)
    (ha : alignment.val.isPowerOfTwo) (hm : mask.val = alignment.val - 1) :
    (x &&& (~~~mask)).val = alignDown x.val alignment.val := by
  have hapos : 0 < alignment.val := Nat.pos_of_isPowerOfTwo ha
  unfold Nat.isPowerOfTwo at ha
  obtain ⟨k, hk⟩ := ha
  have halign : alignment.bv = 2#64 ^ k := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_pow, BitVec.toNat_ofNat]
    change alignment.val = (2 % 2^64) ^ k % 2^64
    norm_num
    rw [← hk]
    exact (Nat.mod_eq_of_lt alignment.hBounds).symm
  have hmask : mask.bv = alignment.bv - 1#64 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_sub_of_le (by change 1 ≤ alignment.val; omega)]
    exact hm
  have hlow : (x.bv &&& mask.bv).toNat = x.val % alignment.val := by
    rw [hmask, halign, BitVec.and_two_pow_sub_one_eq_mod, ← halign]
    rfl
  have hsplit : x.bv &&& ~~~mask.bv = x.bv - (x.bv &&& mask.bv) := by
    apply BitVec.eq_sub_iff_add_eq.mpr
    rw [BitVec.add_eq_or_of_and_eq_zero]
    · simp [← BitVec.and_or_distrib_left]
    · ext i
      simp [Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]
  change (x.bv &&& ~~~mask.bv).toNat = _
  rw [hsplit, BitVec.toNat_sub_of_le]
  · exact congrArg (x.val - ·) hlow
  · simp only [BitVec.le_def, hlow]
    exact Nat.mod_le _ _

/-- There is an aligned start whose entire requested range lies in this slot. -/
def Fits (slot : AddressRange) (size alignment : Nat) : Prop :=
  ∃ start, slot.start.val ≤ start ∧ start % alignment = 0 ∧
    start + (size - 1) ≤ slot.end.val

theorem fits_forward_iff (slot : AddressRange) (size alignment : Nat)
    (ha : 0 < alignment) :
    Fits slot size alignment ↔ alignUp slot.start.val alignment + (size - 1) ≤ slot.end.val := by
  constructor
  · rintro ⟨start, hs, hm, he⟩
    have := alignUp_le ha hm hs
    omega
  · intro he
    exact ⟨_, le_alignUp _ _, alignUp_mod _ _ ha, he⟩

theorem fits_reverse_iff (slot : AddressRange) (size alignment : Nat) :
    Fits slot size alignment ↔ size - 1 ≤ slot.end.val ∧
      slot.start.val ≤ alignDown (slot.end.val - (size - 1)) alignment := by
  constructor
  · rintro ⟨start, hs, hm, he⟩
    have := le_alignDown hm (show start ≤ slot.end.val - (size - 1) by omega)
    omega
  · rintro ⟨hsize, hstart⟩
    refine ⟨_, hstart, alignDown_mod _ _, ?_⟩
    have := alignDown_le (slot.end.val - (size - 1)) alignment
    omega

@[step]
theorem forward_fit_spec (slot : AddressRange) (size alignment : U64)
    (hs : 0 < size.val) (ha : 0 < alignment.val) :
    internal_allocate_with_align.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool.call_mut
      (alignment, size) slot ⦃ b predicate => predicate = (alignment, size) ∧
        (b = true ↔ Fits slot size.val alignment.val) ⦄ := by
  unfold internal_allocate_with_align.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool.call_mut
  step as ⟨r, hr⟩
  split
  · have hr0 : slot.start.val % alignment.val = 0 := by
      change 0 = slot.start.val % alignment.val at hr
      exact hr.symm
    step as ⟨n, hn⟩
    have hadd := U64.checked_add_bv_spec slot.start n
    cases he : U64.checked_add slot.start n <;>
      simp [he] at hadd <;>
      simp [lift, core.option.Option.is_some_and,
        internal_allocate_with_align.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once,
        fits_forward_iff slot _ _ ha, alignUp, hr0] <;> scalar_tac
  · have hrne : slot.start.val % alignment.val ≠ 0 := by
      intro hz
      have hzero : r = 0#u64 := by scalar_tac
      contradiction
    have hrlt : r.val < alignment.val := by rw [hr]; exact Nat.mod_lt _ ha
    step as ⟨n, hn⟩
    have hchecked := U64.checked_add_bv_spec slot.start n
    cases he : U64.checked_add slot.start n with
    | none =>
      simp [he] at hchecked
      simp [lift, core.option.Option.and_then, core.option.Option.is_some_and,
        fits_forward_iff slot _ _ ha, alignUp, hrne]
      scalar_tac
    | some base =>
      simp [he] at hchecked
      simp only [lift, bind_ok, core.option.Option.and_then,
        internal_allocate_with_align.closure.closure.Insts.CoreOpsFunctionFnOnceTupleU64OptionU64.call_once]
      step as ⟨offset, hoffset⟩
      have hchecked' := U64.checked_add_bv_spec base offset
      cases he' : U64.checked_add base offset <;>
        simp [he'] at hchecked' <;>
        simp [core.option.Option.is_some_and,
          internal_allocate_with_align.closure.closure_1.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once,
          fits_forward_iff slot _ _ ha, alignUp, hrne] <;> scalar_tac

@[step]
theorem reverse_fit_spec (slot : AddressRange) (size alignment : U64)
    (hs : 0 < size.val) (ha : alignment.val.isPowerOfTwo) :
    internal_allocate_with_align.closure_1.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool.call_mut
      (size, alignment) slot ⦃ b predicate => predicate = (size, alignment) ∧
        (b = true ↔ Fits slot size.val alignment.val) ⦄ := by
  unfold internal_allocate_with_align.closure_1.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool.call_mut
  step as ⟨n, hn⟩
  have hsub := U64.checked_sub_bv_spec slot.end n
  cases he : U64.checked_sub slot.end n with
  | none =>
    simp [he] at hsub
    simp [lift, core.option.Option.is_some_and, fits_reverse_iff]
    scalar_tac
  | some value =>
    simp [he] at hsub
    simp [lift, core.option.Option.is_some_and,
      internal_allocate_with_align.closure_1.closure.Insts.CoreOpsFunctionFnOnceTupleU64Bool.call_once]
    have hapos := Nat.pos_of_isPowerOfTwo ha
    step as ⟨mask, hm⟩
    have hmask := mask_alignDown value alignment mask ha hm
    simp only [UScalar.val_and] at hmask
    simp [fits_reverse_iff]
    rw [hmask, hsub.2.1, hn]
    omega

/-! ### Ordered search -/

/-- The result is the first matching element, or there are no matches. -/
def FirstMatch {T : Type} (p : T → Prop) (xs : List T) (result : Option T) : Prop :=
  match result with
  | none => ∀ x ∈ xs, ¬p x
  | some x => ∃ before after, xs = before ++ x :: after ∧
      (∀ y ∈ before, ¬p y) ∧ p x

theorem FirstMatch.mem {T : Type} {p : T → Prop} {xs : List T} {x : T}
    (h : FirstMatch p xs (some x)) : x ∈ xs ∧ p x := by
  obtain ⟨before, after, rfl, _, hx⟩ := h
  exact ⟨by simp, hx⟩

theorem FirstMatch.skip {T : Type} {p : T → Prop} {xs : List T} {x : T} {r : Option T}
    (hx : ¬p x) (h : FirstMatch p xs r) : FirstMatch p (x :: xs) r := by
  cases r with
  | none => simpa [FirstMatch] using And.intro hx h
  | some y =>
    obtain ⟨before, after, rfl, hb, hy⟩ := h
    exact ⟨x :: before, after, rfl, by simpa using And.intro hx hb, hy⟩

/-- A finite iterator search terminates and returns its first match.
    The representation parameter covers both ascending and descending traversal. -/
theorem find_spec {I P T : Type} (iterInst : core.iter.traits.iterator.Iterator I T)
    (predInst : core.ops.function.FnMut P T Bool)
    (repr : List T → I)
    (hnext : ∀ xs, iterInst.next (repr xs) =
      match xs with
      | [] => ok (none, repr [])
      | x :: xs => ok (some x, repr xs))
    (predicate : P) (p : T → Prop) (xs : List T)
    (hp : ∀ x ∈ xs, predInst.call_mut predicate x
      ⦃ b predicate' => predicate' = predicate ∧ (b = true ↔ p x) ⦄) :
    _root_.core.iter.traits.iterator.Iterator.find.default iterInst predInst (repr xs) predicate
      ⦃ result _rest => FirstMatch p xs result ⦄ := by
  induction xs with
  | nil =>
    rw [_root_.core.iter.traits.iterator.Iterator.find.default.eq_def, hnext]
    simp [FirstMatch]
  | cons x xs ih =>
    rw [_root_.core.iter.traits.iterator.Iterator.find.default.eq_def, hnext]
    step with hp x (by simp) as ⟨b, predicate', he, hb⟩
    subst predicate'
    split
    · simp only [WP.spec_ok]
      exact ⟨[], xs, rfl, by simp, hb.mp (by assumption)⟩
    · have hn : ¬p x := by simpa using mt hb.mpr (by assumption)
      step with ih (fun y hy => hp y (by simp [hy])) as ⟨result, rest, hr⟩
      exact hr.skip hn

/-- The actual iterator search and clone sequence used by the translated helper. -/
def findSlot (rs : List AddressRange) (size alignment : U64) (reverse : Bool) :
    Result (Option AddressRange) := do
  if reverse then
    let (result, _) ←
      _root_.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.find
        (resources.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT AddressRange)
        internal_allocate_with_align.closure_1.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool
        ⟨rs⟩ (size, alignment)
    _root_.core.option.OptionShared0T.cloned AddressRange.Insts.CoreCloneClone result
  else
    let (result, _) ←
      _root_.core.iter.traits.iterator.Iterator.find.default
        (resources.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT AddressRange)
        internal_allocate_with_align.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool
        rs (alignment, size)
    _root_.core.option.OptionShared0T.cloned AddressRange.Insts.CoreCloneClone result

@[step]
theorem cloned_range_spec (value : Option AddressRange) :
    _root_.core.option.OptionShared0T.cloned AddressRange.Insts.CoreCloneClone value
      ⦃ result => result = value ⦄ := by
  cases value <;> simp [_root_.core.option.OptionShared0T.cloned,
    AddressRange.Insts.CoreCloneClone.clone]

@[step]
theorem findSlot_spec (rs : List AddressRange) (size alignment : U64) (reverse : Bool)
    (hs : 0 < size.val) (ha : alignment.val.isPowerOfTwo) :
    findSlot rs size alignment reverse ⦃ result =>
      FirstMatch (fun slot => Fits slot size.val alignment.val)
        (if reverse then rs.reverse else rs) result ⦄ := by
  unfold findSlot
  cases reverse with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    step with find_spec
      (resources.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT AddressRange)
      internal_allocate_with_align.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool
      (fun xs => xs) (by intro xs; cases xs <;> rfl) (alignment, size)
      (fun slot => Fits slot size.val alignment.val) rs
      (fun slot _ => forward_fit_spec slot size alignment hs (Nat.pos_of_isPowerOfTwo ha))
    step
    simp_all
  | true =>
    simp only [↓reduceIte, _root_.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.find]
    let repr := fun xs : List AddressRange =>
      (⟨xs.reverse⟩ : core.iter.adapters.rev.Rev (List AddressRange))
    let revIter : core.iter.traits.iterator.Iterator
        (core.iter.adapters.rev.Rev (List AddressRange)) AddressRange :=
      { next := Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next
          (resources.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT AddressRange) }
    have hnext : ∀ xs, revIter.next (repr xs) = match xs with
            | [] => ok (none, repr [])
            | x :: xs => ok (some x, repr xs) := by
      intro xs
      cases xs <;> simp [revIter, Aeneas.Std.core.iter.adapters.rev.Rev.Insts.CoreIterTraitsIteratorIterator.next,
        _root_.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsDouble_endedDoubleEndedIteratorSharedT.next_back,
        repr]
    have hsearch := find_spec revIter
      internal_allocate_with_align.closure_1.Insts.CoreOpsFunctionFnMutTupleShared2Shared3AddressRangeBool
      repr (by
        intro xs
        cases xs with
        | nil => exact hnext []
        | cons x xs => exact hnext (x :: xs)) (size, alignment) (fun slot => Fits slot size.val alignment.val) rs.reverse
      (fun slot _ => reverse_fit_spec slot size alignment hs ha)
    simp only [revIter, repr, List.reverse_reverse] at hsearch
    step with hsearch
    step
    simp_all

/-! ### Aligned allocation -/

/-- A whole allocation fits within one free slot, at an aligned address. -/
def Placement (rs : List AddressRange) (size alignment start : Nat) : Prop :=
  ∃ slot ∈ rs, slot.start.val ≤ start ∧ start % alignment = 0 ∧
    start + (size - 1) ≤ slot.end.val

/-- A placement also satisfies any alignment dividing its original alignment. -/
theorem Placement.of_dvd {rs : List AddressRange} {size alignment start smaller : Nat}
    (h : Placement rs size alignment start) (hd : smaller ∣ alignment) :
    Placement rs size smaller start := by
  obtain ⟨slot, hm, hs, ha, he⟩ := h
  exact ⟨slot, hm, hs, Nat.mod_eq_zero_of_dvd (hd.trans (Nat.dvd_of_mod_eq_zero ha)), he⟩

/-- Forward allocation chooses the lowest possible address; reverse chooses the highest. -/
def BestPlacement (rs : List AddressRange) (size alignment : Nat) (reverse : Bool)
    (start : Nat) : Prop :=
  Placement rs size alignment start ∧
    ∀ candidate, Placement rs size alignment candidate →
      if reverse then candidate ≤ start else start ≤ candidate

private def selectedStart (slot : AddressRange) (size alignment : Nat) (reverse : Bool) : Nat :=
  if reverse then alignDown (slot.end.val - (size - 1)) alignment
  else alignUp slot.start.val alignment

private theorem selectedStart_fits (slot : AddressRange) (size alignment : Nat)
    (reverse : Bool) (ha : 0 < alignment) (hf : Fits slot size alignment) :
    slot.start.val ≤ selectedStart slot size alignment reverse ∧
      selectedStart slot size alignment reverse % alignment = 0 ∧
      selectedStart slot size alignment reverse + (size - 1) ≤ slot.end.val := by
  cases reverse with
  | false =>
    exact ⟨le_alignUp _ _, alignUp_mod _ _ ha, (fits_forward_iff slot _ _ ha).mp hf⟩
  | true =>
    have hf := (fits_reverse_iff slot size alignment).mp hf
    have hl := alignDown_le (slot.end.val - (size - 1)) alignment
    exact ⟨hf.2, alignDown_mod _ _, by simp only [selectedStart, ↓reduceIte]; omega⟩

private theorem selectedStart_best (slot : AddressRange) (size alignment : Nat)
    (reverse : Bool) (ha : 0 < alignment) (candidate : Nat)
    (hc : slot.start.val ≤ candidate ∧ candidate % alignment = 0 ∧
      candidate + (size - 1) ≤ slot.end.val) :
    if reverse then candidate ≤ selectedStart slot size alignment reverse
    else selectedStart slot size alignment reverse ≤ candidate := by
  cases reverse with
  | false => exact alignUp_le ha hc.2.1 hc.1
  | true => exact le_alignDown hc.2.1 (by omega)

/-- The final start-address calculation in the generated function. -/
private def alignedStart (slot : AddressRange) (size alignment : U64) (reverse : Bool) :
    Result U64 := do
  if reverse then
    let n ← size - 1#u64
    let start ← slot.end - n
    let mask ← alignment - 1#u64
    let mask ← lift (~~~mask)
    ok (start &&& mask)
  else
    let remainder ← slot.start % alignment
    match remainder with
    | 0#uscalar => ok slot.start
    | _ =>
      let offset ← alignment - remainder
      slot.start + offset

@[step]
private theorem alignedStart_spec (slot : AddressRange) (size alignment : U64)
    (reverse : Bool) (hs : 0 < size.val) (ha : alignment.val.isPowerOfTwo)
    (hf : Fits slot size.val alignment.val) :
    alignedStart slot size alignment reverse ⦃ start =>
      start.val = selectedStart slot size.val alignment.val reverse ⦄ := by
  have hapos := Nat.pos_of_isPowerOfTwo ha
  unfold alignedStart
  cases reverse with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    have hf := (fits_forward_iff slot _ _ hapos).mp hf
    step as ⟨r, hr⟩
    split
    · change 0 = slot.start.val % alignment.val at hr
      simp [selectedStart, alignUp, hr.symm]
    · have hrne : slot.start.val % alignment.val ≠ 0 := by
        intro hz
        have hzero : r = 0#u64 := by scalar_tac
        contradiction
      have hrlt : r.val < alignment.val := by rw [hr]; exact Nat.mod_lt _ hapos
      simp only [alignUp, hrne, ↓reduceIte] at hf
      step as ⟨offset, hoffset⟩
      step
      simp_all [selectedStart, alignUp]
  | true =>
    simp only [↓reduceIte]
    have hf := (fits_reverse_iff slot _ _).mp hf
    step as ⟨n, hn⟩
    step as ⟨start, hstart⟩
    step as ⟨mask, hm⟩
    simp only [lift, bind_ok, WP.spec_ok]
    rw [mask_alignDown start alignment mask ha hm]
    simp_all [selectedStart]

private theorem firstMatch_best (rs : List AddressRange) (slot : AddressRange)
    (size alignment : Nat) (reverse : Bool) (hv : ValidRegions rs) (ha : 0 < alignment)
    (hmatch : FirstMatch (fun r => Fits r size alignment)
      (if reverse then rs.reverse else rs) (some slot)) :
    BestPlacement rs size alignment reverse (selectedStart slot size alignment reverse) := by
  have hmem := hmatch.mem
  have hm : slot ∈ rs := by cases reverse <;> simpa using hmem.1
  have hfit := selectedStart_fits slot size alignment reverse ha hmem.2
  refine ⟨⟨slot, hm, hfit⟩, ?_⟩
  intro candidate ⟨r, hr, hc⟩
  have hfr : Fits r size alignment := ⟨candidate, hc⟩
  have hr' : r ∈ (if reverse then rs.reverse else rs) := by
    cases reverse <;> simpa using hr
  have horder : (if reverse then rs.reverse else rs).Pairwise
      (fun r s => if reverse then s.end.val < r.start.val else r.end.val < s.start.val) := by
    cases reverse <;> simpa [List.pairwise_reverse] using hv.2
  obtain ⟨before, after, hxs, hmiss, _⟩ := hmatch
  rw [hxs] at hr' horder
  rcases List.mem_append.mp hr' with hb | hr'
  · exact False.elim (hmiss r hb hfr)
  · rcases List.mem_cons.mp hr' with rfl | hr'
    · exact selectedStart_best _ size alignment reverse ha candidate hc
    · have hsep := (List.pairwise_cons.mp (List.pairwise_append.mp horder).2.1).1 r hr'
      cases reverse <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega

/-- Successful allocation removes precisely the requested range and inserts its tag.
    The selected start is the lowest/highest feasible aligned address. -/
def AlignedAllocation (self : AddressAllocator) (size : U64) (allocation : resources.Alloc)
    (tag : String) (alignment : Nat) (reverse : Bool) (start : U64) (a : AddressAllocator) : Prop :=
  BestPlacement self.regions size.val alignment reverse start.val ∧
    ∃ range : AddressRange, range.start = start ∧
      range.end.val + 1 = start.val + size.val ∧
      a.pools = self.pools ∧ a.min_align = self.min_align ∧
      a.preferred_align = self.preferred_align ∧
      a.allocs = Finmap.insert allocation (range, tag) self.allocs ∧
      ValidRegions a.regions ∧
      ∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∧ ¬range.containsModel addr

/-- Error precedence follows the API: duplicate key, zero size, bad effective alignment,
    then lack of a fitting slot. Every error preserves the allocator. -/
def AlignedAllocationOutcome (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (alignment : Nat) (reverse : Bool)
    (result : core.result.Result U64 resources.Error) (a : AddressAllocator) : Prop :=
  if allocation ∈ self.allocs then result = .Err (.ExistingAlloc allocation) ∧ a = self
  else if size.val = 0 then result = .Err .AllocSizeZero ∧ a = self
  else if ¬alignment.isPowerOfTwo then result = .Err .BadAlignment ∧ a = self
  else match result with
    | .Ok start => AlignedAllocation self size allocation tag alignment reverse start a
    | .Err error => error = .OutOfSpace ∧ a = self ∧
        ¬∃ start, Placement self.regions size.val alignment start

/-- Allocation leaves the recorded pools and alignment policy unchanged. -/
theorem AlignedAllocationOutcome.pools_alignments {self a : AddressAllocator} {size : U64}
    {allocation : resources.Alloc} {tag : String} {alignment : Nat} {reverse : Bool}
    {result : core.result.Result U64 resources.Error}
    (h : AlignedAllocationOutcome self size allocation tag alignment reverse result a) :
    a.pools = self.pools ∧ a.min_align = self.min_align ∧ a.preferred_align = self.preferred_align := by
  unfold AlignedAllocationOutcome at h
  split at h
  · simp [h.2]
  · split at h
    · simp [h.2]
    · split at h
      · simp [h.2]
      · cases result with
        | Err error => simp [h.2.1]
        | Ok start =>
          obtain ⟨range, _, _, hpools, hmin, hpref, _⟩ := h.2
          exact ⟨hpools, hmin, hpref⟩

/-- A successful allocation under a fresh key preserves the full invariant. -/
theorem AlignedAllocation.wellFormed {self a : AddressAllocator} {size start : U64}
    {allocation : resources.Alloc} {tag : String} {alignment : Nat} {reverse : Bool}
    (h : AlignedAllocation self size allocation tag alignment reverse start a)
    (hwf : WellFormed self) (hfresh : allocation ∉ self.allocs) : WellFormed a := by
  obtain ⟨slot, hslot, hfit⟩ := h.1.1
  obtain ⟨range, hstart, hsize, hpools, hmin, hpref, hallocs, hregions, hcover⟩ := h.2
  apply hwf.allocate ⟨hregions, by simpa [hmin] using hwf.minAlign,
    by simpa [hpref] using hwf.preferredAlign,
    by simpa [hmin, hpref] using hwf.alignOrder⟩ hfresh hpools hallocs ?_ hcover
  intro addr ha
  refine ⟨slot, hslot, ?_⟩
  simp only [AddressRange.containsModel, hstart] at ha ⊢
  omega

/-- Allocation preserves well-formedness on both success and expected errors. -/
theorem AlignedAllocationOutcome.wellFormed {self a : AddressAllocator} {size : U64}
    {allocation : resources.Alloc} {tag : String} {alignment : Nat} {reverse : Bool}
    {result : core.result.Result U64 resources.Error}
    (h : AlignedAllocationOutcome self size allocation tag alignment reverse result a)
    (hwf : WellFormed self) : WellFormed a := by
  unfold AlignedAllocationOutcome at h
  split at h
  · simpa [h.2] using hwf
  · rename_i hfresh
    split at h
    · simpa [h.2] using hwf
    · split at h
      · simpa [h.2] using hwf
      · cases result with
        | Ok start => exact h.wellFormed hwf hfresh
        | Err error => simpa [h.2.1] using hwf

/-- The generated continuation after the iterator search. -/
private noncomputable def allocateFound (self : AddressAllocator) (size : U64) (allocation : resources.Alloc)
    (tag : String) (alignment : U64) (reverse : Bool) (region : Option AddressRange) :
    Result (core.result.Result U64 resources.Error × AddressAllocator) := do
  match region with
  | none => ok (.Err .OutOfSpace, self)
  | some slot =>
    let start ← alignedStart slot size alignment reverse
    let offset ← size - 1#u64
    let end_ ← start + offset
    internal_allocate_from_slot self slot ⟨start, end_⟩ allocation tag

private theorem allocateFound_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (alignment : U64) (reverse : Bool)
    (region : Option AddressRange) (hv : ValidRegions self.regions)
    (hs : 0 < size.val) (ha : alignment.val.isPowerOfTwo)
    (hmatch : FirstMatch (fun r => Fits r size.val alignment.val)
      (if reverse then self.regions.reverse else self.regions) region) :
    allocateFound self size allocation tag alignment reverse region ⦃ result a =>
      match result with
      | .Ok start => AlignedAllocation self size allocation tag alignment.val reverse start a
      | .Err error => error = .OutOfSpace ∧ a = self ∧
          ¬∃ start, Placement self.regions size.val alignment.val start ⦄ := by
  cases region with
  | none =>
    simp [allocateFound]
    intro start
    rintro ⟨slot, hm, hfit⟩
    have hm' : slot ∈ (if reverse then self.regions.reverse else self.regions) := by
      cases reverse <;> simpa using hm
    exact hmatch slot hm' ⟨start, hfit⟩
  | some slot =>
    have hselected := hmatch.mem
    have hm : slot ∈ self.regions := by cases reverse <;> simpa using hselected.1
    have hfit := selectedStart_fits slot size.val alignment.val reverse
      (Nat.pos_of_isPowerOfTwo ha) hselected.2
    have hbest := firstMatch_best self.regions slot size.val alignment.val reverse hv
      (Nat.pos_of_isPowerOfTwo ha) hmatch
    unfold allocateFound
    step with alignedStart_spec slot size alignment reverse hs ha hselected.2 as ⟨start, hstart⟩
    step as ⟨offset, hoffset⟩
    step as ⟨end_, he⟩
    step with internal_allocate_from_slot_spec self slot ⟨start, end_⟩ allocation tag hv hm
      (by simp only [AddressRange.isEmptyModel]; omega)
      (by simp only; omega) as ⟨result, a, hresult, hpools, hmin, hpref, hallocs, hvalid, hcover⟩
    subst result
    refine ⟨?_, ⟨start, end_⟩, rfl, ?_, hpools, hmin, hpref, hallocs, hvalid, hcover⟩
    · simpa only [hstart] using hbest
    · simp only
      omega

/-- Total correctness in both directions. Expected errors preserve the allocator. -/
@[step]
theorem internal_allocate_with_align_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (alignment : U64) (reverse : Bool)
    (hv : ValidRegions self.regions) :
    internal_allocate_with_align self size allocation tag alignment reverse ⦃ result a =>
      AlignedAllocationOutcome self size allocation tag
        (max self.min_align.val alignment.val) reverse result a ⦄ := by
  unfold internal_allocate_with_align
  step as ⟨effective, heffective⟩
  step with contains_key_spec self allocation as ⟨exists_, hexists⟩
  split
  · simp_all [AlignedAllocationOutcome]
  · have hfresh : allocation ∉ self.allocs := by simp_all
    split
    · simp_all [AlignedAllocationOutcome]
    · have hs : 0 < size.val := by scalar_tac
      step as ⟨power, hpower⟩
      split
      · have ha : effective.val.isPowerOfTwo := by simp_all
        simp only [_root_.alloc.collections.btree.set.BTreeSet.iter,
          core.iter.traits.iterator.Iterator.rev.trait_default,
          core.iter.traits.iterator.Iterator.rev.default, bind_ok]
        change (do
          let region ← findSlot self.regions size effective reverse
          allocateFound self size allocation tag effective reverse region) ⦃ result a =>
            AlignedAllocationOutcome self size allocation tag
              (max self.min_align.val alignment.val) reverse result a ⦄
        step with findSlot_spec self.regions size effective reverse hs ha as ⟨region, hmatch⟩
        step with allocateFound_spec self size allocation tag effective reverse region hv hs ha hmatch
          as ⟨result, a, hresult⟩
        simpa [AlignedAllocationOutcome, hfresh, Nat.ne_of_gt hs, ← heffective, ha] using hresult
      · simp_all [AlignedAllocationOutcome, Nat.ne_of_gt hs]

/-! ### Preferred alignment fallback -/

open scoped Classical in
/-- The shared two-attempt allocation sequence, parameterized by search direction. -/
private theorem allocate_preferred_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (reverse : Bool)
    (hwf : WellFormed self) :
    (do
      let (result, a) ← internal_allocate_with_align self size allocation tag self.preferred_align reverse
      match result with
      | .Ok _ => ok (result, a)
      | .Err _ => internal_allocate_with_align a size allocation tag a.min_align reverse)
      ⦃ result a =>
        let alignment := if ∃ start, Placement self.regions size.val self.preferred_align.val start
          then self.preferred_align.val else self.min_align.val
        AlignedAllocationOutcome self size allocation tag alignment reverse result a ⦄ := by
  classical
  rcases hwf.toStructuralInvariant with ⟨hv, hmin, hpref, horder⟩
  have hmax := max_eq_right horder
  step with internal_allocate_with_align_spec self size allocation tag self.preferred_align reverse hv
    as ⟨result, a, hfirst⟩
  cases result with
  | Ok start =>
    have hsuccess : AlignedAllocation self size allocation tag self.preferred_align.val reverse start a := by
      simp only [AlignedAllocationOutcome, hmax, hpref, not_true_eq_false, ↓reduceIte] at hfirst
      split_ifs at hfirst <;> simp_all
    have hfits : ∃ candidate, Placement self.regions size.val self.preferred_align.val candidate :=
      ⟨start.val, hsuccess.1.1⟩
    simpa only [hfits, ↓reduceIte, WP.spec_ok, WP.uncurry', hmax] using hfirst
  | Err error =>
    have hself : a = self := by
      simp only [AlignedAllocationOutcome, hmax, hpref, not_true_eq_false, ↓reduceIte] at hfirst
      split_ifs at hfirst <;> tauto
    subst a
    step with internal_allocate_with_align_spec self size allocation tag self.min_align reverse hv as ⟨result, a, hsecond⟩
    by_cases hk : allocation ∈ self.allocs
    · simpa [AlignedAllocationOutcome, hk] using hsecond
    by_cases hz : size.val = 0
    · simpa [AlignedAllocationOutcome, hk, hz] using hsecond
    have hno : ¬∃ start, Placement self.regions size.val self.preferred_align.val start := by
      simp only [AlignedAllocationOutcome, hmax, if_neg hk, if_neg hz,
        hpref, not_true_eq_false, ↓reduceIte] at hfirst
      exact hfirst.2.2
    simpa only [hno, ↓reduceIte, max_self] using hsecond

/-! ### Public allocation -/

/-- Explicit-alignment forward allocation chooses the lowest feasible address.
    Expected errors preserve the allocator. -/
@[step]
theorem allocate_with_align_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (alignment : U64)
    (hwf : WellFormed self) :
    allocate_with_align self size allocation tag alignment ⦃ result a =>
      WellFormed a ∧ AlignedAllocationOutcome self size allocation tag
        (max self.min_align.val alignment.val) false result a ⦄ := by
  unfold allocate_with_align
  step with internal_allocate_with_align_spec self size allocation tag alignment false hwf.validRegions
    as ⟨result, a, hresult⟩
  exact ⟨hresult.wellFormed hwf, hresult⟩

/-- Explicit-alignment reverse allocation chooses the highest feasible address.
    Expected errors preserve the allocator. -/
@[step]
theorem reverse_allocate_with_align_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (alignment : U64)
    (hwf : WellFormed self) :
    reverse_allocate_with_align self size allocation tag alignment ⦃ result a =>
      WellFormed a ∧ AlignedAllocationOutcome self size allocation tag
        (max self.min_align.val alignment.val) true result a ⦄ := by
  unfold reverse_allocate_with_align
  step with internal_allocate_with_align_spec self size allocation tag alignment true hwf.validRegions
    as ⟨result, a, hresult⟩
  exact ⟨hresult.wellFormed hwf, hresult⟩

open scoped Classical in
/-- Prefer the lowest address admitting the preferred alignment; use the minimum
    alignment only if no preferred-alignment placement exists. Both alignments
    satisfy the constructor's requirements. Expected errors preserve the allocator. -/
@[step]
theorem allocate_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (hwf : WellFormed self) :
    allocate self size allocation tag ⦃ result a =>
      let alignment := if ∃ start, Placement self.regions size.val self.preferred_align.val start
        then self.preferred_align.val else self.min_align.val
      WellFormed a ∧ AlignedAllocationOutcome self size allocation tag alignment false result a ⦄ := by
  unfold allocate allocate_with_align
  simp only [alloc.string.String.Insts.CoreCloneClone.clone, bind_ok]
  apply WP.spec_mono (allocate_preferred_spec self size allocation tag false hwf)
  rintro ⟨result, a⟩ hresult
  exact ⟨hresult.wellFormed hwf, hresult⟩

open scoped Classical in
/-- Prefer the highest address admitting the preferred alignment; use the minimum
    alignment only if no preferred-alignment placement exists. Both alignments
    satisfy the constructor's requirements. Expected errors preserve the allocator. -/
@[step]
theorem reverse_allocate_spec (self : AddressAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (hwf : WellFormed self) :
    reverse_allocate self size allocation tag ⦃ result a =>
      let alignment := if ∃ start, Placement self.regions size.val self.preferred_align.val start
        then self.preferred_align.val else self.min_align.val
      WellFormed a ∧ AlignedAllocationOutcome self size allocation tag alignment true result a ⦄ := by
  unfold reverse_allocate reverse_allocate_with_align
  simp only [alloc.string.String.Insts.CoreCloneClone.clone, bind_ok]
  apply WP.spec_mono (allocate_preferred_spec self size allocation tag true hwf)
  rintro ⟨result, a⟩ hresult
  exact ⟨hresult.wellFormed hwf, hresult⟩

/-! ### Fixed-address allocation -/

/-- The whole requested range lies in a single free slot. -/
def RangeAvailable (rs : List AddressRange) (range : AddressRange) : Prop :=
  ∃ slot ∈ rs, ∀ addr, range.containsModel addr → slot.containsModel addr

/-- The named allocation shares an address with the requested range. -/
def AllocationOverlap (self : AddressAllocator) (range : AddressRange)
    (allocation : resources.Alloc) : Prop :=
  ∃ allocated tag, Finmap.lookup allocation self.allocs = some (allocated, tag) ∧
    ∃ addr, allocated.containsModel addr ∧ range.containsModel addr

/-- Return an overlapping allocation, or establish that none exists. Any overlapping key
    may be returned; no hash-map iteration order is specified. -/
@[step]
theorem find_overlapping_spec (self : AddressAllocator) (range : AddressRange) :
    find_overlapping self range ⦃ result =>
      match result with
      | some allocation => AllocationOverlap self range allocation
      | none => ∀ allocation, ¬AllocationOverlap self range allocation ⦄ := by
  unfold find_overlapping
  step with AddressRange.is_empty_spec range as ⟨empty, hempty⟩
  split
  · simp only [WP.spec_ok]
    rintro allocation ⟨allocated, tag, _, addr, _, hr⟩
    have he := hempty.mp (by assumption)
    simp only [AddressRange.isEmptyModel, AddressRange.containsModel] at *
    omega
  · step with hashMap_iter_spec self.allocs as ⟨entries, hentries⟩
    step with find_spec
      (resources.std.collections.hash.map.Iter.Insts.CoreIterTraitsIteratorIteratorPairSharedAKSharedAV
        resources.Alloc (AddressRange × String))
      find_overlapping.closure.Insts.CoreOpsFunctionFnMutTupleShared1PairShared2AllocShared3PairAddressRangeStringBool
      (fun xs => xs) (by intro xs; cases xs <;> rfl) range
      (fun entry => ∃ addr, entry.2.1.containsModel addr ∧ range.containsModel addr) entries
      (by
        rintro ⟨key, allocated, tag⟩ _
        simp only [find_overlapping.closure.Insts.CoreOpsFunctionFnMutTupleShared1PairShared2AllocShared3PairAddressRangeStringBool.call_mut]
        step with AddressRange.overlaps_spec allocated range
        simp_all) as ⟨entry, rest, hmatch⟩
    cases entry with
    | none =>
      simp only [core.option.Option.map, WP.spec_ok]
      rintro allocation ⟨allocated, tag, hlookup, hoverlap⟩
      apply hmatch (allocation, (allocated, tag)) ((hentries _ _).mpr hlookup)
      simpa only [AddressRange.containsModel, and_assoc] using hoverlap
    | some entry =>
      rcases entry with ⟨key, allocated, tag⟩
      have hm := hmatch.mem
      simp [core.option.Option.map,
        find_overlapping.closure_1.Insts.CoreOpsFunctionFnOnceTuplePairShared0AllocShared1PairAddressRangeStringAlloc.call_once]
      refine ⟨allocated, tag, (hentries _ _).mp hm.1, ?_⟩
      simpa only [AddressRange.containsModel, and_assoc] using hm.2

/-- A successful fixed-address allocation records exactly the requested range and
    removes its addresses from the free regions. Errors preserve the allocator;
    overlap errors identify an actual conflicting allocation. Alignment is ignored. -/
def AllocationAtOutcome (self : AddressAllocator) (range : AddressRange)
    (allocation : resources.Alloc) (tag : String)
    (result : core.result.Result Unit resources.Error) (a : AddressAllocator) : Prop :=
  if allocation ∈ self.allocs then result = .Err (.ExistingAlloc allocation) ∧ a = self
  else if range.isEmptyModel then result = .Err .AllocSizeZero ∧ a = self
  else match result with
    | .Ok () => RangeAvailable self.regions range ∧
        a.pools = self.pools ∧ a.min_align = self.min_align ∧
        a.preferred_align = self.preferred_align ∧
        a.allocs = Finmap.insert allocation (range, tag) self.allocs ∧
        ∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∧ ¬range.containsModel addr
    | .Err error => a = self ∧ ¬RangeAvailable self.regions range ∧
        match error with
        | .ExistingAlloc existing => AllocationOverlap self range existing
        | .OutOfSpace => ∀ existing, ¬AllocationOverlap self range existing
        | _ => False

/-- Fixed-address allocation is correct for every range, including empty ranges
    and ranges ending at `u64::MAX`; it requires no alignment or overflow bounds. -/
@[step]
theorem allocate_at_spec (self : AddressAllocator) (range : AddressRange)
    (allocation : resources.Alloc) (tag : String) (hwf : WellFormed self) :
    allocate_at self range allocation tag ⦃ result a =>
      WellFormed a ∧ AllocationAtOutcome self range allocation tag result a ⦄ := by
  unfold allocate_at
  step with contains_key_spec self allocation as ⟨exists_, hexists⟩
  split
  · simp_all [AllocationAtOutcome]
  · have hfresh : allocation ∉ self.allocs := by simp_all
    step with AddressRange.is_empty_spec range as ⟨empty, hempty⟩
    split
    · simp_all [AllocationAtOutcome]
    · have hn : ¬range.isEmptyModel := by simp_all
      simp only [_root_.alloc.collections.btree.set.BTreeSet.iter, bind_ok]
      step with find_spec
        (resources.alloc.collections.btree.set.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT AddressRange)
        allocate_at.closure.Insts.CoreOpsFunctionFnMutTupleShared1Shared2AddressRangeBool
        (fun xs => xs) (by intro xs; cases xs <;> rfl) range
        (fun slot => ∀ addr, range.containsModel addr → slot.containsModel addr) self.regions
        (by
          intro slot _
          simp only [allocate_at.closure.Insts.CoreOpsFunctionFnMutTupleShared1Shared2AddressRangeBool.call_mut]
          step with AddressRange.contains_range_spec slot range as ⟨b, hb⟩
          rw [hb]
          simp only [hn, not_false_eq_true, true_and]
          constructor
          · intro h addr hr
            simp only [AddressRange.containsModel] at *
            omega
          · intro h
            have hs := h range.start.val
            have he := h range.end.val
            simp only [AddressRange.containsModel, AddressRange.isEmptyModel] at *
            omega) as ⟨slot, rest, hmatch⟩
      cases slot with
      | none =>
        have hunavailable : ¬RangeAvailable self.regions range := by
          rintro ⟨slot, hm, hc⟩
          apply hmatch slot hm
          simpa only [AddressRange.containsModel, and_imp] using hc
        step with find_overlapping_spec self range as ⟨overlap, hoverlap⟩
        cases overlap <;> simp_all [AllocationAtOutcome]
      | some slot =>
        have hmem : slot ∈ self.regions ∧
            ∀ addr, range.containsModel addr → slot.containsModel addr := by
          simpa only [AddressRange.containsModel, and_imp] using hmatch.mem
        have hsub : slot.start.val ≤ range.start.val ∧ range.end.val ≤ slot.end.val := by
          have hs := hmem.2 range.start.val
          have he := hmem.2 range.end.val
          simp only [AddressRange.containsModel, AddressRange.isEmptyModel] at *
          omega
        step with internal_allocate_from_slot_spec self slot range allocation tag hwf.validRegions
          hmem.1 hn hsub as ⟨result, a, hresult, hpools, hmin, hpref, hallocs, hvalid, hcover⟩
        subst result
        simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
        simp only [WP.spec_ok, AllocationAtOutcome, hfresh, hn, ↓reduceIte]
        refine ⟨?_, ⟨slot, hmem⟩, hpools, hmin, hpref, hallocs, hcover⟩
        exact hwf.allocate ⟨hvalid, by simpa [hmin] using hwf.minAlign,
          by simpa [hpref] using hwf.preferredAlign,
          by simpa [hmin, hpref] using hwf.alignOrder⟩ hfresh hpools hallocs
          (fun addr ha => ⟨slot, hmem.1, hmem.2 addr ha⟩) hcover

/-! ### Returning a range to the free regions -/

/-- Endpoint adjacency of nonempty inclusive ranges, using unbounded arithmetic. -/
def AdjacentRanges (r s : AddressRange) : Prop :=
  r.end.val + 1 = s.start.val ∨ s.end.val + 1 = r.start.val

/-- Replace the inserted range and its directly adjacent free neighbors by one
    region containing exactly their addresses. All other regions stay unchanged.
    This does not merge chains of neighbors already adjacent before insertion. -/
def CoalescedInsertion (before : List AddressRange) (slot : AddressRange)
    (after : List AddressRange) : Prop :=
  ∃ merged,
    (∀ addr, merged.containsModel addr ↔ slot.containsModel addr ∨
      ∃ r ∈ before, AdjacentRanges r slot ∧ r.containsModel addr) ∧
    ∀ r, r ∈ after ↔ r = merged ∨ r ∈ before ∧ ¬AdjacentRanges r slot

private def removeMerge (rs : List AddressRange) (region : Option AddressRange) :
    Result (List AddressRange) := do
  match region with
  | none => ok rs
  | some r =>
    let (_, rest) ← _root_.alloc.collections.btree.set.BTreeSet.remove
      resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      (resources.core.borrow.Borrow.Blanket AddressRange)
      AddressRange.Insts.CoreCmpOrd AddressRange.Insts.CoreCmpOrd rs r
    ok rest

/-- The update performed after both overlap checks have succeeded. -/
private def mergeSlot (self : AddressAllocator) (slot : AddressRange)
    (left right : Option AddressRange) : Result (core.result.Result Unit resources.Error × AddressAllocator) := do
  let rs ← removeMerge self.regions left
  let rs ← removeMerge rs right
  let merged := { slot with start := (left.getD slot).start, «end» := (right.getD slot).end }
  let (_, rs) ← _root_.alloc.collections.btree.set.BTreeSet.insert
    resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone AddressRange.Insts.CoreCmpOrd rs merged
  ok (.Ok (), { self with regions := rs })

/-- The checked endpoint comparison on either side of the inserted range. -/
private def checkNeighbor (slot : AddressRange) (lower : Bool) (found : Option AddressRange) :
    Result (core.result.Result (Option AddressRange) resources.Error) := do
  match found with
  | none => ok (.Ok none)
  | some r =>
    let endpoint ← lift (if lower then U64.checked_add r.end 1#u64 else U64.checked_sub r.start 1#u64)
    match endpoint with
    | none => ok (.Err (.RegionOverlap slot))
    | some endpoint =>
      let o ← lift (if lower then core.cmp.impls.OrdU64.cmp endpoint slot.start
        else core.cmp.impls.OrdU64.cmp slot.end endpoint)
      match o with
      | .lt => ok (.Ok none)
      | .eq => ok (.Ok (some r))
      | .gt => ok (.Err (.RegionOverlap slot))

private def insertBody (self : AddressAllocator) (slot : AddressRange) :
    Result (core.result.Result Unit resources.Error × AddressAllocator) := do
  let left ← neighbor self.regions slot true
  let checkedLeft ← checkNeighbor slot true left
  match checkedLeft with
  | .Err error => ok (.Err error, self)
  | .Ok left =>
    let right ← neighbor self.regions slot false
    let checkedRight ← checkNeighbor slot false right
    match checkedRight with
    | .Err error => ok (.Err error, self)
    | .Ok right => mergeSlot self slot left right

set_option maxHeartbeats 1000000 in
/-- Share the repeated checks and update in the extracted function. -/
private theorem insert_at_eq (self : AddressAllocator) (slot : AddressRange) :
    insert_at self slot = (do
      let empty ← AddressRange.is_empty slot
      if empty then ok (.Err .AllocSizeZero, self) else insertBody self slot) := by
  simp only [insert_at, insertBody, neighbor, checkNeighbor, mergeSlot, removeMerge,
    core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
    Aeneas.Std.bind_assoc, Bool.false_eq_true, ↓reduceIte, bind_ok, lift,
    core.option.Option.ok_or, core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
    core.convert.FromSame.from]
  repeat' first
    | rfl
    | (apply congrArg (Std.bind _); funext x)
    | (rename_i x; rcases (x : Bool × List AddressRange) with ⟨added, rest⟩; simp)
    | (simp only [bind_tc_ok])
    | (split <;> try simp_all only [Aeneas.Std.bind_assoc, bind_ok,
        Option.getD_none, Option.getD_some])

private theorem removeMerge_spec (rs : List AddressRange) (region : Option AddressRange)
    (hv : ValidRegions rs) (hm : ∀ r ∈ region, r ∈ rs) :
    removeMerge rs region ⦃ rest => ValidRegions rest ∧
      ∀ r, r ∈ rest ↔ r ∈ rs ∧ r ∉ region ⦄ := by
  cases region with
  | none => simp [removeMerge, hv]
  | some r =>
    unfold removeMerge
    step with remove_region_spec rs r hv (hm r rfl)
    simp_all [eq_comm]

private def MergeSide (rs : List AddressRange) (slot : AddressRange) (lower : Bool)
    (selected : Option AddressRange) : Prop :=
  ∀ r, r ∈ selected ↔ r ∈ rs ∧
    (if lower then r.end.val + 1 = slot.start.val else slot.end.val + 1 = r.start.val)

private theorem mergeSlot_spec (self : AddressAllocator) (slot : AddressRange)
    (left right : Option AddressRange) (hwf : StructuralInvariant self) (hn : ¬slot.isEmptyModel)
    (hl : MergeSide self.regions slot true left) (hr : MergeSide self.regions slot false right)
    (hd : ∀ r ∈ self.regions, DisjointRanges slot r) :
    mergeSlot self slot left right ⦃ result a => result = .Ok () ∧ StructuralInvariant a ∧
      a.pools = self.pools ∧ a.allocs = self.allocs ∧ a.min_align = self.min_align ∧
      a.preferred_align = self.preferred_align ∧
      (∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∨ slot.containsModel addr) ∧
      CoalescedInsertion self.regions slot a.regions ⦄ := by
  have hlm : ∀ r ∈ left, r ∈ self.regions := fun r hm => ((hl r).mp hm).1
  have hrm : ∀ r ∈ right, r ∈ self.regions := fun r hm => ((hr r).mp hm).1
  have hlr : ∀ r ∈ right, r ∉ left := by
    intro r hr' hl'
    have h1 := ((hl r).mp hl').2
    have h2 := ((hr r).mp hr').2
    have hnon := hwf.validRegions.1 r (hrm r hr')
    simp only [Bool.false_eq_true, ↓reduceIte, AddressRange.isEmptyModel] at *
    omega
  let merged : AddressRange := ⟨(left.getD slot).start, (right.getD slot).end⟩
  have hc : ∀ addr, merged.containsModel addr ↔ slot.containsModel addr ∨
      (∃ r ∈ left, r.containsModel addr) ∨ (∃ r ∈ right, r.containsModel addr) := by
    intro addr
    cases left with
    | none =>
      cases right with
      | none => simp [merged]
      | some r =>
        have h := ((hr r).mp rfl).2
        have hnon := hwf.validRegions.1 r (hrm r rfl)
        simp [merged, AddressRange.containsModel, AddressRange.isEmptyModel] at *
        omega
    | some l =>
      have h := ((hl l).mp rfl).2
      have hnon := hwf.validRegions.1 l (hlm l rfl)
      cases right with
      | none =>
        simp [merged, AddressRange.containsModel, AddressRange.isEmptyModel] at *
        omega
      | some r =>
        have h' := ((hr r).mp rfl).2
        have hnon' := hwf.validRegions.1 r (hrm r rfl)
        simp [merged, AddressRange.containsModel, AddressRange.isEmptyModel] at *
        omega
  have hmerged : ¬merged.isEmptyModel := by
    have h := (hc slot.start.val).mpr (Or.inl (by
      simp only [AddressRange.containsModel, AddressRange.isEmptyModel] at *; omega))
    simp only [AddressRange.containsModel, AddressRange.isEmptyModel] at *
    omega
  unfold mergeSlot
  step with removeMerge_spec self.regions left hwf.validRegions hlm as ⟨rs, hv, hm⟩
  step with removeMerge_spec rs right hv
    (fun r hr' => (hm r).mpr ⟨hrm r hr', hlr r hr'⟩) as ⟨rest, hvrest, hmrest⟩
  have hdisjoint : ∀ r ∈ rest, DisjointRanges merged r := by
    intro r hmem
    obtain ⟨⟨hmem, hleft⟩, hright⟩ := (hmrest r).mp hmem |>.imp_left ((hm r).mp)
    have hnon := hwf.validRegions.1 r hmem
    have hds := hd r hmem
    have hdl : ∀ l ∈ left, DisjointRanges l r := fun l h =>
      hwf.validRegions.disjoint (hlm l h) hmem (fun he => hleft (he ▸ h))
    have hdr : ∀ l ∈ right, DisjointRanges l r := fun l h =>
      hwf.validRegions.disjoint (hrm l h) hmem (fun he => hright (he ▸ h))
    have hcontra : ¬∃ addr, merged.containsModel addr ∧ r.containsModel addr := by
      rintro ⟨addr, ha, hrange⟩
      rcases (hc addr).mp ha with hs | ⟨l, hl', ha⟩ | ⟨l, hr', ha⟩
      · simp only [DisjointRanges, AddressRange.containsModel] at *; omega
      · have h := hdl l hl'
        simp only [DisjointRanges, AddressRange.containsModel] at *; omega
      · have h := hdr l hr'
        simp only [DisjointRanges, AddressRange.containsModel] at *; omega
    simp only [DisjointRanges, AddressRange.containsModel, AddressRange.isEmptyModel] at *
    by_contra h
    exact hcontra ⟨max merged.start.val r.start.val, by omega⟩
  step with insert_region_spec rest merged hvrest hmerged hdisjoint as ⟨added, regions, _, hvalid, hmem⟩
  refine ⟨⟨hvalid, hwf.minAlign, hwf.preferredAlign, hwf.alignOrder⟩, ?_⟩
  constructor
  · intro addr
    constructor
    · rintro ⟨r, hr', ha⟩
      rcases (hmem r).mp hr' with rfl | hr'
      · rcases (hc addr).mp ha with hs | ⟨l, hl', ha⟩ | ⟨r, hr', ha⟩
        · exact Or.inr hs
        · exact Or.inl ⟨l, hlm l hl', ha⟩
        · exact Or.inl ⟨r, hrm r hr', ha⟩
      · exact Or.inl ⟨r, ((hm r).mp ((hmrest r).mp hr').1).1, ha⟩
    · rintro (⟨r, hr', ha⟩ | hs)
      · by_cases hl' : r ∈ left
        · exact ⟨merged, (hmem merged).mpr (Or.inl rfl), (hc addr).mpr (Or.inr (Or.inl ⟨r, hl', ha⟩))⟩
        · by_cases hr'' : r ∈ right
          · exact ⟨merged, (hmem merged).mpr (Or.inl rfl), (hc addr).mpr (Or.inr (Or.inr ⟨r, hr'', ha⟩))⟩
          · exact ⟨r, (hmem r).mpr (Or.inr ((hmrest r).mpr ⟨(hm r).mpr ⟨hr', hl'⟩, hr''⟩)), ha⟩
      · exact ⟨merged, (hmem merged).mpr (Or.inl rfl), (hc addr).mpr (Or.inl hs)⟩
  · refine ⟨merged, ?_, ?_⟩
    · intro addr
      rw [hc]
      have hs : ∀ r, r ∈ left ∨ r ∈ right ↔ r ∈ self.regions ∧ AdjacentRanges r slot := by
        intro r
        simp only [hl r, hr r, Bool.false_eq_true, ↓reduceIte, AdjacentRanges]
        tauto
      simp only [← and_assoc]
      simp_rw [← hs]
      simp only [or_and_right, exists_or]
    · intro r
      rw [hmem, hmrest, hm, hl r, hr r]
      simp only [Bool.false_eq_true, ↓reduceIte, AdjacentRanges]
      tauto

private theorem neighbor_separated (rs : List AddressRange) (slot : AddressRange)
    (lower : Bool) (found : Option AddressRange) (hv : ValidRegions rs)
    (h : Neighbor rs slot lower found)
    (hsep : ∀ r ∈ found, if lower then r.end.val < slot.start.val else slot.end.val < r.start.val) :
    ∀ r ∈ rs, (if lower then ¬slot.ltModel r else slot.ltModel r) → DisjointRanges slot r := by
  cases found with
  | none => intro r hr hs; exact False.elim (h r hr hs)
  | some selected =>
    intro r hr hs
    have hselected := hv.1 selected h.1
    have hbound := hsep selected rfl
    rcases h.2.2 r hr hs with rfl | horder
    all_goals
      cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte, DisjointRanges,
        AddressRange.isEmptyModel] at * <;> omega

private theorem neighbor_overlap (rs : List AddressRange) (slot selected : AddressRange)
    (lower : Bool) (hv : ValidRegions rs) (hn : ¬slot.isEmptyModel)
    (h : Neighbor rs slot lower (some selected))
    (hbad : if lower then slot.start.val ≤ selected.end.val else selected.start.val ≤ slot.end.val) :
    ∃ addr, Covers rs addr ∧ slot.containsModel addr := by
  have hnon := hv.1 selected h.1
  refine ⟨max slot.start.val selected.start.val, ⟨selected, h.1, ?_⟩, ?_⟩
  all_goals
    have hside := h.2.1
    cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte, AddressRange.ltModel,
      AddressRange.containsModel, AddressRange.isEmptyModel] at * <;> omega

/-- Once a neighbor is separated from the input, any adjacent region on that
    side must be that neighbor. -/
private theorem neighbor_adjacent_iff (rs : List AddressRange) (slot : AddressRange)
    (lower : Bool) (found : Option AddressRange) (hv : ValidRegions rs) (hn : ¬slot.isEmptyModel)
    (h : Neighbor rs slot lower found)
    (hsep : ∀ r ∈ found, if lower then r.end.val < slot.start.val else slot.end.val < r.start.val) :
    ∀ r, (r ∈ rs ∧ (if lower then r.end.val + 1 = slot.start.val else slot.end.val + 1 = r.start.val)) ↔
      (r ∈ found ∧ (if lower then r.end.val + 1 = slot.start.val else slot.end.val + 1 = r.start.val)) := by
  intro r
  constructor
  · rintro ⟨hm, hadj⟩
    refine ⟨?_, hadj⟩
    have hrn := hv.1 r hm
    have hside : if lower then ¬slot.ltModel r else slot.ltModel r := by
      cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte,
        AddressRange.ltModel, AddressRange.isEmptyModel] at * <;> omega
    cases found with
    | none => exact False.elim (h r hm hside)
    | some selected =>
      rcases h.2.2 r hm hside with he | ho
      · simpa using he.symm
      · have hbound := hsep selected rfl
        have hnon := hv.1 selected h.1
        cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte,
          AddressRange.isEmptyModel] at * <;> omega
  · rintro ⟨hm, hadj⟩
    cases found with
    | none => simp at hm
    | some selected =>
      have he : selected = r := Option.mem_some_iff.mp hm
      subst r
      exact ⟨h.1, hadj⟩

private theorem checkNeighbor_spec (rs : List AddressRange) (slot : AddressRange)
    (lower : Bool) (found : Option AddressRange) (hv : ValidRegions rs) (hn : ¬slot.isEmptyModel)
    (h : Neighbor rs slot lower found) :
    checkNeighbor slot lower found ⦃ result =>
      match result with
      | .Err error => error = .RegionOverlap slot ∧ ∃ addr, Covers rs addr ∧ slot.containsModel addr
      | .Ok selected => MergeSide rs slot lower selected ∧
          ∀ r ∈ rs, (if lower then ¬slot.ltModel r else slot.ltModel r) → DisjointRanges slot r ⦄ := by
  cases found with
  | none =>
    simp only [checkNeighbor, WP.spec_ok]
    have hm := neighbor_adjacent_iff rs slot lower none hv hn h (by simp)
    exact ⟨by intro r; simpa using (hm r).symm,
      neighbor_separated rs slot lower none hv h (by simp)⟩
  | some r =>
    have hgood (hsep : if lower then r.end.val < slot.start.val else slot.end.val < r.start.val) :=
      neighbor_separated rs slot lower (some r) hv h (by simpa using hsep)
    have hmerge (hsep : if lower then r.end.val < slot.start.val else slot.end.val < r.start.val) :=
      neighbor_adjacent_iff rs slot lower (some r) hv hn h (by simpa using hsep)
    have hbad := neighbor_overlap rs slot r lower hv hn h
    cases lower with
    | false =>
      have hc := U64.checked_sub_bv_spec r.start 1#u64
      cases he : U64.checked_sub r.start 1#u64 with
      | none =>
        simp [he] at hc
        simp [checkNeighbor, he, lift]
        exact hbad (by simp only [Bool.false_eq_true, ↓reduceIte]; scalar_tac)
      | some endpoint =>
        simp [he] at hc
        simp only [checkNeighbor, Bool.false_eq_true, ↓reduceIte, he, lift, bind_ok,
          core.cmp.impls.OrdU64.cmp, compare, compareOfLessAndEq]
        split_ifs with hlt heq
        · simp only [WP.spec_ok]
          have hm := hmerge (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
          refine ⟨?_, hgood (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)⟩
          intro s
          rw [hm s]
          simp only [Option.not_mem_none, Option.mem_some_iff, Bool.false_eq_true, ↓reduceIte]
          constructor
          · exact False.elim
          · rintro ⟨rfl, hadj⟩; omega
        · simp only [WP.spec_ok]
          have hm := hmerge (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
          refine ⟨?_, hgood (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)⟩
          intro s
          rw [hm s]
          simp only [Option.mem_some_iff, Bool.false_eq_true, ↓reduceIte]
          constructor
          · rintro rfl; exact ⟨rfl, by omega⟩
          · exact And.left
        · simp only [WP.spec_ok, true_and]
          exact hbad (by simp only [Bool.false_eq_true, ↓reduceIte]; omega)
    | true =>
      have hc := U64.checked_add_bv_spec r.end 1#u64
      cases he : U64.checked_add r.end 1#u64 with
      | none =>
        simp [he] at hc
        simp [checkNeighbor, he, lift]
        exact hbad (by simp only [↓reduceIte]; scalar_tac)
      | some endpoint =>
        simp [he] at hc
        simp only [checkNeighbor, ↓reduceIte, he, lift, bind_ok,
          core.cmp.impls.OrdU64.cmp, compare, compareOfLessAndEq]
        split_ifs with hlt heq
        · simp only [WP.spec_ok]
          have hm := hmerge (by simp only [↓reduceIte]; omega)
          refine ⟨?_, hgood (by simp only [↓reduceIte]; omega)⟩
          intro s
          rw [hm s]
          simp only [Option.not_mem_none, Option.mem_some_iff, ↓reduceIte]
          constructor
          · exact False.elim
          · rintro ⟨rfl, hadj⟩; omega
        · simp only [WP.spec_ok]
          have hm := hmerge (by simp only [↓reduceIte]; omega)
          refine ⟨?_, hgood (by simp only [↓reduceIte]; omega)⟩
          intro s
          rw [hm s]
          simp only [Option.mem_some_iff, ↓reduceIte]
          constructor
          · rintro rfl; exact ⟨rfl, by omega⟩
          · exact And.left
        · simp only [WP.spec_ok, true_and]
          exact hbad (by simp only [↓reduceIte]; omega)

/-- Insertion adds precisely the requested addresses to the free set and coalesces
    the input with its directly adjacent free neighbors. It rejects empty ranges
    and any overlap with an existing free region, without mutation.
    The helper does not check pool membership or modify allocation records. -/
def InsertAtOutcome (self : AddressAllocator) (slot : AddressRange)
    (result : core.result.Result Unit resources.Error) (a : AddressAllocator) : Prop :=
  if slot.isEmptyModel then result = .Err .AllocSizeZero ∧ a = self
  else match result with
    | .Err error => error = .RegionOverlap slot ∧ a = self ∧
        ∃ addr, Covers self.regions addr ∧ slot.containsModel addr
    | .Ok () => (∀ addr, ¬(Covers self.regions addr ∧ slot.containsModel addr)) ∧
        a.pools = self.pools ∧ a.allocs = self.allocs ∧ a.min_align = self.min_align ∧
        a.preferred_align = self.preferred_align ∧
        (∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∨ slot.containsModel addr) ∧
        CoalescedInsertion self.regions slot a.regions

/-- Total correctness of free-region insertion, including both endpoint extremes.
    The free-region and alignment invariant is preserved on success and error. -/
@[step]
theorem insert_at_spec (self : AddressAllocator) (slot : AddressRange) (hwf : StructuralInvariant self) :
    insert_at self slot ⦃ result a => StructuralInvariant a ∧ InsertAtOutcome self slot result a ⦄ := by
  rw [insert_at_eq]
  step with AddressRange.is_empty_spec slot as ⟨empty, hempty⟩
  split
  · simp_all [InsertAtOutcome]
  · have hn : ¬slot.isEmptyModel := by simp_all
    unfold insertBody
    step with neighbor_spec self.regions slot true hwf.validRegions hn as ⟨left, hleft⟩
    step with checkNeighbor_spec self.regions slot true left hwf.validRegions hn hleft
      as ⟨checkedLeft, hl⟩
    cases checkedLeft with
    | Err error => simpa [InsertAtOutcome, hn, hwf] using hl
    | Ok left =>
      step with neighbor_spec self.regions slot false hwf.validRegions hn as ⟨right, hright⟩
      step with checkNeighbor_spec self.regions slot false right hwf.validRegions hn hright
        as ⟨checkedRight, hr⟩
      cases checkedRight with
      | Err error => simpa [InsertAtOutcome, hn, hwf] using hr
      | Ok right =>
        have hd : ∀ r ∈ self.regions, DisjointRanges slot r := by
          intro r hm
          by_cases h : slot.ltModel r
          · exact hr.2 r hm h
          · exact hl.2 r hm h
        step with mergeSlot_spec self slot left right hwf hn hl.1 hr.1 hd
          as ⟨result, a, hresult, hwfa, hpools, hallocs, hmin, hpref, hcover, hcoalesce⟩
        subst result
        simp only [InsertAtOutcome, hn, ↓reduceIte]
        refine ⟨hwfa, ?_, hpools, hallocs, hmin, hpref, hcover, hcoalesce⟩
        rintro addr ⟨⟨r, hm, ha⟩, hs⟩
        have h := hd r hm
        simp only [DisjointRanges, AddressRange.containsModel] at *
        omega

/-! ### Releasing allocations -/

/-- Release returns the recorded range, erases its key, and coalesces it into the
    free regions. A missing key leaves the allocator unchanged. If a recorded
    range is empty or already overlaps free space, insertion fails after the key
    has been erased; the free regions are then unchanged. -/
def ReleaseOutcome (self : AddressAllocator) (allocation : resources.Alloc)
    (result : core.result.Result AddressRange resources.Error) (a : AddressAllocator) : Prop :=
  match Finmap.lookup allocation self.allocs with
  | none => result = .Err (.BadAlloc allocation) ∧ a = self
  | some (range, _) =>
    a.pools = self.pools ∧ a.min_align = self.min_align ∧
    a.preferred_align = self.preferred_align ∧
    a.allocs = Finmap.erase allocation self.allocs ∧
    if range.isEmptyModel then result = .Err .AllocSizeZero ∧ a.regions = self.regions
    else match result with
      | .Err error => error = .RegionOverlap range ∧ a.regions = self.regions ∧
          ∃ addr, Covers self.regions addr ∧ range.containsModel addr
      | .Ok released => released = range ∧
          (∀ addr, ¬(Covers self.regions addr ∧ range.containsModel addr)) ∧
          (∀ addr, Covers a.regions addr ↔ Covers self.regions addr ∨ range.containsModel addr) ∧
          CoalescedInsertion self.regions range a.regions

/-- Release preserves the full partition. Recorded nonempty allocations cannot
    overlap free space, so their insertion succeeds. Empty records contain no addresses. -/
@[step]
theorem release_spec (self : AddressAllocator) (allocation : resources.Alloc)
    (hwf : WellFormed self) :
    release self allocation ⦃ result a => WellFormed a ∧ ReleaseOutcome self allocation result a ⦄ := by
  unfold release
  step with remove_alloc_spec self allocation as ⟨found, allocs, hremove⟩
  cases hlookup : Finmap.lookup allocation self.allocs with
  | none =>
    simp only [hlookup] at hremove
    rcases hremove with ⟨rfl, rfl⟩
    simp [ReleaseOutcome, hlookup, hwf]
  | some entry =>
    rcases entry with ⟨range, tag⟩
    simp only [hlookup] at hremove
    rcases hremove with ⟨rfl, rfl⟩
    have hwf' : StructuralInvariant { self with allocs := Finmap.erase allocation self.allocs } :=
      ⟨hwf.validRegions, hwf.minAlign, hwf.preferredAlign, hwf.alignOrder⟩
    step with insert_at_spec { self with allocs := Finmap.erase allocation self.allocs } range hwf'
      as ⟨inserted, a, hwfa, houtcome⟩
    cases inserted with
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok]
      by_cases hn : range.isEmptyModel
      · simp only [InsertAtOutcome, hn, ↓reduceIte] at houtcome
        rcases houtcome with ⟨he, rfl⟩
        have hwell := hwf.release hwfa hlookup rfl rfl (by
          intro addr
          have hempty : ¬range.containsModel addr := by
            simp only [AddressRange.isEmptyModel, AddressRange.containsModel] at *
            omega
          simp [hempty])
        simp_all [ReleaseOutcome]
      · simp only [InsertAtOutcome, hn, ↓reduceIte] at houtcome
        rcases houtcome with ⟨he, rfl, addr, hfree, hrange⟩
        exact False.elim (hwf.freeDisjoint allocation range tag hlookup addr hfree hrange)
    | Ok u =>
      cases u
      have hn : ¬range.isEmptyModel := by
        intro he
        simp [InsertAtOutcome, he] at houtcome
      simp only [InsertAtOutcome, hn, ↓reduceIte] at houtcome
      rcases houtcome with ⟨hdisjoint, hpools, hallocs, hmin, hpref, hcover, hcoalesce⟩
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok, WP.spec_ok,
        ReleaseOutcome, hlookup, hn, ↓reduceIte]
      exact ⟨hwf.release hwfa hlookup hpools hallocs hcover,
        hpools, hmin, hpref, hallocs, rfl, hdisjoint, hcover, hcoalesce⟩

/-- A containing release either finds no allocation and leaves the allocator
    unchanged, or releases one whole allocation containing the address. If
    allocations overlap, any matching key may be chosen. -/
def ReleaseContainingOutcome (self : AddressAllocator) (value : U64)
    (result : core.result.Result AddressRange resources.Error) (a : AddressAllocator) : Prop :=
  (result = .Err .OutOfSpace ∧ a = self ∧
    ∀ allocation range tag, Finmap.lookup allocation self.allocs = some (range, tag) →
      ¬range.containsModel value.val) ∨
  ∃ allocation range tag, Finmap.lookup allocation self.allocs = some (range, tag) ∧
    range.containsModel value.val ∧ ReleaseOutcome self allocation result a

@[step]
theorem release_containing_spec (self : AddressAllocator) (value : U64)
    (hwf : WellFormed self) :
    release_containing self value ⦃ result a =>
      WellFormed a ∧ ReleaseContainingOutcome self value result a ⦄ := by
  unfold release_containing
  step with find_overlapping_spec self ⟨value, value⟩ as ⟨allocation, hoverlap⟩
  cases allocation with
  | none =>
    simp only [WP.spec_ok]
    refine ⟨hwf, Or.inl ⟨rfl, rfl, ?_⟩⟩
    intro allocation range tag hlookup hcontains
    exact hoverlap allocation ⟨range, tag, hlookup, value.val, hcontains, le_refl _, le_refl _⟩
  | some allocation =>
    obtain ⟨range, tag, hlookup, addr, hrange, hvalue⟩ := hoverlap
    have he : addr = value.val := Nat.le_antisymm hvalue.2 hvalue.1
    subst addr
    step with release_spec self allocation hwf as ⟨result, a, hwfa, hrelease⟩
    exact ⟨hwfa, Or.inr ⟨allocation, range, tag, hlookup, hrange, hrelease⟩⟩

/-! ### PCI offsets -/

/-- A PCI offset resolves exactly when a nonempty request fits in the recorded BAR.
    Non-PCI or missing keys are invalid; other rejected requests are out of bounds. -/
def PciOffsetOutcome (self : AddressAllocator) (allocation : resources.Alloc)
    (offset size : U64) (result : core.result.Result U64 resources.Error) : Prop :=
  match allocation with
  | .PciBar _ _ _ _ =>
    match Finmap.lookup allocation self.allocs with
    | none => result = .Err (.InvalidAlloc allocation)
    | some (range, _) =>
      let start := range.start.val + offset.val
      let end_ := start + (size.val - 1)
      if 0 < size.val ∧ range.start.val ≤ start ∧ end_ ≤ range.end.val then
        ∃ address, result = .Ok address ∧ address.val = start
      else result = .Err .OutOfBounds
  | _ => result = .Err (.InvalidAlloc allocation)

/-- Total correctness of PCI offset lookup, without allocator invariant assumptions. -/
@[step]
theorem address_from_pci_offset_spec (self : AddressAllocator) (allocation : resources.Alloc)
    (offset size : U64) :
    address_from_pci_offset self allocation offset size ⦃ result =>
      PciOffsetOutcome self allocation offset size result ⦄ := by
  cases allocation <;> unfold address_from_pci_offset
  all_goals try simp [PciOffsetOutcome]
  rename_i bus dev func bar
  step with get_alloc_spec self (.PciBar bus dev func bar) as ⟨found, hfound⟩
  subst found
  cases hlookup : Finmap.lookup (.PciBar bus dev func bar) self.allocs with
  | none => simp
  | some entry =>
    rcases entry with ⟨range, tag⟩
    have hadd := U64.checked_add_bv_spec range.start offset
    cases haddress : U64.checked_add range.start offset with
    | none =>
      simp only [haddress] at hadd
      simp [lift, haddress, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from]
      scalar_tac
    | some address =>
      simp only [haddress] at hadd
      simp [lift, haddress,
        core.result.Result.Insts.CoreOpsTry.branch]
      step with AddressRange.from_start_and_size_spec address size as ⟨request, hrequest⟩
      by_cases hz : size.val = 0
      · simp only [hz, ↓reduceIte] at hrequest
        obtain ⟨requested, rfl, hempty⟩ := hrequest
        simp only [core.option.Option.ok_or_some, bind_ok]
        step with AddressRange.contains_range_spec range requested as ⟨contains, hcontains⟩
        simp_all
      · by_cases hbound : address.val + (size.val - 1) ≤ U64.max
        · simp only [hz, hbound, ↓reduceIte] at hrequest
          obtain ⟨requested, rfl, hstart, hend, hnonempty⟩ := hrequest
          simp only [core.option.Option.ok_or_some, bind_ok]
          step with AddressRange.contains_range_spec range requested as ⟨contains, hcontains⟩
          split <;> simp_all
          scalar_tac
        · simp only [hz, hbound, ↓reduceIte] at hrequest
          subst request
          simp [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from]
          scalar_tac

end resources.address_allocator.AddressAllocator
