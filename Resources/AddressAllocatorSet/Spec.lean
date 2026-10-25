module
public import Resources.AddressAllocator.Spec
@[expose] public section
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
open resources.address_allocator
open resources.address_range

namespace resources.address_allocator.AddressAllocatorSet

/-- Each component is well formed. Pools and allocation keys need not be
    disjoint between different allocators. -/
def WellFormed (self : AddressAllocatorSet) : Prop :=
  ∀ allocator ∈ self.allocators.val, AddressAllocator.WellFormed allocator

/-- Try the allocators in slice order. On success, only the first successful
    component changes, according to the single-allocator contract. On failure,
    every component rejects the request and the entire set is unchanged; return
    the last component's error, or `OutOfSpace` for an empty set. -/
def AllocationAtOutcome (self : AddressAllocatorSet) (range : AddressRange)
    (allocation : resources.Alloc) (tag : String)
    (result : core.result.Result Unit resources.Error) (a : AddressAllocatorSet) : Prop :=
  let attempt := fun before result after =>
    AddressAllocator.AllocationAtOutcome before range allocation tag result after
  match result with
  | .Ok () => ∃ (i : Fin self.allocators.val.length) (updated : AddressAllocator),
      (∀ before ∈ self.allocators.val.take i, ∃ error, attempt before (.Err error) before) ∧
      attempt self.allocators.val[i] (.Ok ()) updated ∧
      a.allocators = self.allocators.setAtNat i updated
  | .Err error => a = self ∧
      (∀ before ∈ self.allocators.val, ∃ error, attempt before (.Err error) before) ∧
      match self.allocators.val.getLast? with
      | none => error = .OutOfSpace
      | some before => attempt before (.Err error) before

/-- A failed search preserves every allocator, including its allocations and tags. -/
theorem AllocationAtOutcome.error_unchanged {self a : AddressAllocatorSet} {range : AddressRange}
    {allocation : resources.Alloc} {tag : String} {error : resources.Error}
    (h : AllocationAtOutcome self range allocation tag (.Err error) a) : a = self := h.1

/-- The set succeeds exactly when some component can satisfy the request.
    A duplicate key or overlap in an earlier component does not stop the search. -/
theorem AllocationAtOutcome.success_iff {self a : AddressAllocatorSet} {range : AddressRange}
    {allocation : resources.Alloc} {tag : String} {result : core.result.Result Unit resources.Error}
    (h : AllocationAtOutcome self range allocation tag result a) :
    result = .Ok () ↔ ∃ before ∈ self.allocators.val,
      allocation ∉ before.allocs ∧ ¬range.isEmptyModel ∧
        AddressAllocator.RangeAvailable before.regions range := by
  constructor
  · intro hresult
    subst result
    obtain ⟨i, updated, _, hsuccess, _⟩ := h
    exact ⟨self.allocators.val[i], List.getElem_mem i.isLt, hsuccess.success_iff.mp rfl⟩
  · rintro ⟨before, hmem, hcan⟩
    cases result with
    | Ok u => cases u; rfl
    | Err error =>
      obtain ⟨previousError, hfailed⟩ := h.2.1 before hmem
      have hcontra := hfailed.success_iff.mpr hcan
      cases hcontra

/-- Construction preserves the entire allocator slice, including its order and
    each allocator's state. Ending the mutable borrow writes back exactly the
    final set's slice. This also covers an empty slice and needs no allocator
    well-formedness assumption. -/
@[step]
theorem new_spec (allocators : Slice AddressAllocator) :
    new allocators ⦃ self back =>
      self.allocators = allocators ∧
      ∀ updated, back updated = updated.allocators ⦄ := by
  simp only [new, WP.spec_ok]
  exact ⟨rfl, fun _ => rfl⟩

/-- The first successful allocator supplies the address and is the only component
    updated. If every allocator rejects the request, the set is unchanged and the
    last error is returned, or `OutOfSpace` for an empty set. Each component uses
    the single-allocator contract, including preferred-alignment fallback. -/
def AllocationOutcome (self : AddressAllocatorSet) (size : U64) (allocation : resources.Alloc)
    (tag : String) (result : core.result.Result U64 resources.Error)
    (updated : AddressAllocatorSet) : Prop :=
  match result with
  | .Ok address =>
    ∃ (i : Fin self.allocators.val.length) (allocated : AddressAllocator),
      AddressAllocator.AllocationOutcome self.allocators.val[i]
        size allocation tag false (.Ok address) allocated ∧
      (∀ j : Fin self.allocators.val.length, j < i →
        ∃ error, AddressAllocator.AllocationOutcome self.allocators.val[j]
          size allocation tag false (.Err error) self.allocators.val[j]) ∧
      updated.allocators = self.allocators.setAtNat i.val allocated
  | .Err error =>
    updated = self ∧
    (∀ i : Fin self.allocators.val.length,
      ∃ e, AddressAllocator.AllocationOutcome self.allocators.val[i]
        size allocation tag false (.Err e) self.allocators.val[i]) ∧
    match self.allocators.val.getLast? with
    | none => error = .OutOfSpace
    | some allocator =>
      AddressAllocator.AllocationOutcome allocator size allocation tag false (.Err error) allocator

/-- Each component's pool accounting and disjointness remain valid. This does
    not require different components to have disjoint pools or distinct keys. -/
theorem AllocationOutcome.wellFormed {self updated size allocation tag result}
    (h : AllocationOutcome self size allocation tag result updated)
    (hwf : WellFormed self) : WellFormed updated := by
  unfold WellFormed
  cases result with
  | Ok address =>
    obtain ⟨i, allocated, houtcome, _, hstate⟩ := h
    rw [hstate]
    simp only [Slice.setAtNat, Slice.from_val]
    intro a ha
    rcases List.mem_or_eq_of_mem_set ha with ha | rfl
    · exact hwf a ha
    · exact houtcome.wellFormed (hwf _ (List.getElem_mem i.isLt))
  | Err error =>
    obtain ⟨rfl, _⟩ := h
    exact hwf

/-- Failed components form an unchanged prefix, so pending mutable borrows can
    write back their original components without changing the final slice. -/
private theorem allocate_loop_spec (s : Slice AddressAllocator) (i : Nat)
    (back : core.slice.iter.IterMut AddressAllocator → core.slice.iter.IterMut AddressAllocator)
    (size : U64) (allocation : resources.Alloc) (tag : String) (lastError : resources.Error)
    (hi : i ≤ s.val.length) (hwf : WellFormed ⟨s⟩)
    (hfailed : ∀ j : Fin s.val.length, j.val < i →
      ∃ error, AddressAllocator.AllocationOutcome s.val[j]
        size allocation tag false (.Err error) s.val[j])
    (hlast : if h : i = 0 then lastError = .OutOfSpace else
      AddressAllocator.AllocationOutcome (s.val[i - 1]'(by omega))
        size allocation tag false (.Err lastError) (s.val[i - 1]'(by omega))) :
    allocate_loop ⟨s, i⟩ back size allocation tag (.Err lastError) ⦃ result final =>
      ∃ out, final = back out ∧ (∃ rest, out.slice.val = s.val.take i ++ rest) ∧
        AllocationOutcome ⟨s⟩ size allocation tag result ⟨out.slice⟩ ⦄ := by
  unfold allocate_loop
  rw [loop.eq_def]
  simp only [allocate_loop.body, core.slice.iter.IteratorIterMut.next, Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp [alloc.string.String.Insts.CoreCloneClone.clone]
    step with AddressAllocator.allocate_spec s.val[i] size allocation tag
      (hwf _ (List.getElem_mem hnext)) as ⟨pair, hupdated, houtcome⟩
    rcases pair with ⟨result, updated⟩
    dsimp only at hupdated houtcome
    cases result with
    | Ok start =>
      simp [core.result.Result.is_ok]
      refine ⟨⟨s.setAtNat i updated, i + 1⟩, rfl, ⟨updated :: s.val.drop (i + 1), ?_⟩, ?_⟩
      · simp [Slice.setAtNat, List.set_eq_take_append_cons_drop, hnext]
      · exact ⟨⟨i, hnext⟩, updated, houtcome, hfailed, rfl⟩
    | Err error =>
      have heq := houtcome.eq_of_err
      subst updated
      simp [core.result.Result.is_ok]
      have hrec := allocate_loop_spec s (i + 1)
        (fun it => back { it with slice := it.slice.setAtNat i s.val[i] })
        size allocation tag error (by omega) hwf (by
          intro j hj
          by_cases he : j.val = i
          · exact ⟨error, by simpa [he] using houtcome⟩
          · exact hfailed j (by omega)) (by simpa using houtcome)
      simp only [allocate_loop, allocate_loop.body, core.slice.iter.IteratorIterMut.next,
        Slice.len_val, Slice.length, alloc.string.String.Insts.CoreCloneClone.clone,
        core.result.Result.is_ok, bind_ok] at hrec
      apply WP.spec_mono hrec
      rintro ⟨result, final⟩ ⟨out, hfinal, ⟨rest, hout⟩, hresult⟩
      refine ⟨out, ?_, ⟨s.val[i] :: rest, ?_⟩, hresult⟩
      · have hwrite : out.slice.setAtNat i s.val[i] = out.slice := by
          apply Slice.ext
          simp only [Slice.setAtNat, Slice.from_val]
          rw [hout, List.take_succ_eq_append_getElem hnext, List.append_assoc]
          simp [List.set_append_right, List.length_take, Nat.min_eq_left hi]
        simpa only [hwrite] using hfinal
      · simpa only [List.take_succ_eq_append_getElem hnext, List.append_assoc,
          List.singleton_append] using hout
  · rename_i hdone
    have he : i = s.val.length := by omega
    simp
    refine ⟨⟨s, i⟩, rfl, ⟨[], by simp [he]⟩, rfl, fun j => hfailed j (by omega), ?_⟩
    by_cases hz : i = 0
    · have hempty : s.val = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [hempty] using (by simpa [hz] using hlast : lastError = .OutOfSpace)
    · simp only [hz, ↓reduceDIte] at hlast
      have hlastIndex : s.val.length - 1 < s.val.length := by omega
      simpa only [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlastIndex, he]
        using hlast
termination_by s.val.length - i

/-- Total correctness of ordered allocation, including empty sets and failures
    other than `OutOfSpace`. Only component well-formedness is required. The
    returned outer borrow writes back the final set unchanged. -/
@[step]
theorem allocate_spec (self : AddressAllocatorSet) (size : U64)
    (allocation : resources.Alloc) (tag : String) (hwf : WellFormed self) :
    allocate self size allocation tag ⦃ result updated back =>
      AllocationOutcome self size allocation tag result updated ∧
      WellFormed updated ∧
      ∀ final, back final = final ⦄ := by
  unfold allocate
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with allocate_loop_spec self.allocators 0 (fun it => it) size allocation tag .OutOfSpace
    (by omega) hwf (by simp) (by simp) as ⟨result, final, rest, hprefix, houtcome⟩
  simpa only [implies_true, and_true] using
    And.intro houtcome (houtcome.wellFormed hwf)

private theorem restore_prefix_element {T : Type} (s t : Slice T) (i : Nat)
    (hi : i < s.val.length) (hprefix : t.val.take (i + 1) = s.val.take (i + 1)) :
    t.setAtNat i s.val[i] = t := by
  have he := congrArg (fun xs => xs[i]?) hprefix
  simp only [List.getElem?_take, Nat.lt_add_one, ↓reduceIte,
    List.getElem?_eq_getElem hi] at he
  have ht : i < t.val.length := List.getElem?_eq_some_iff.mp he |>.1
  have hget : t.val[i] = s.val[i] := by simpa only [List.getElem?_eq_getElem ht, Option.some.injEq] using he
  apply Slice.ext
  simp [Slice.setAtNat, ← hget]

private theorem allocate_at_loop_spec (s : Slice AddressAllocator) (i : Nat)
    (back : core.slice.iter.IterMut AddressAllocator → core.slice.iter.IterMut AddressAllocator)
    (range : AddressRange) (allocation : resources.Alloc) (tag : String)
    (lastError : resources.Error) (hi : i ≤ s.val.length)
    (hwf : WellFormed ⟨s⟩)
    (hprevious : ∀ before ∈ s.val.take i, ∃ error,
      AddressAllocator.AllocationAtOutcome before range allocation tag (.Err error) before)
    (hlast : match (s.val.take i).getLast? with
      | none => lastError = .OutOfSpace
      | some before => AddressAllocator.AllocationAtOutcome before range allocation tag
          (.Err lastError) before)
    (hback : ∀ it, it.slice.val.take i = s.val.take i → (back it).slice = it.slice) :
    allocate_at_loop ⟨s, i⟩ back range allocation tag (.Err lastError) ⦃ result it =>
      WellFormed ⟨it.slice⟩ ∧ AllocationAtOutcome ⟨s⟩ range allocation tag result ⟨it.slice⟩ ⦄ := by
  unfold allocate_at_loop
  rw [loop.eq_def]
  dsimp only
  rw [allocate_at_loop.body, core.slice.iter.IteratorIterMut.next]
  dsimp only
  split
  · rename_i hnext
    change i < s.val.length at hnext
    simp [alloc.string.String.Insts.CoreCloneClone.clone]
    step with AddressAllocator.allocate_at_spec s.val[i] range allocation tag
      (hwf _ (List.getElem_mem hnext)) as ⟨pair, hwupdated, hout⟩
    rcases pair with ⟨result, updated⟩
    dsimp only at hwupdated hout
    cases result with
    | Ok u =>
      cases u
      simp [core.result.Result.is_ok]
      have hb := hback ⟨s.setAtNat i updated, i + 1⟩ (by
        simp [Slice.setAtNat, List.take_set_of_le (Nat.le_refl i)])
      simp only [hb]
      constructor
      · intro allocator hmem
        simp only [Slice.setAtNat, Slice.from_val] at hmem
        rcases List.mem_or_eq_of_mem_set hmem with hm | rfl
        · exact hwf _ hm
        · exact hwupdated
      · exact ⟨⟨i, hnext⟩, updated, hprevious, hout, rfl⟩
    | Err error =>
      have heq := hout.error_unchanged
      subst updated
      simp [core.result.Result.is_ok]
      apply allocate_at_loop_spec s (i + 1) _ range allocation tag error (by omega) hwf
      · intro before hmem
        simp only [List.take_succ_eq_append_getElem hnext, List.mem_append,
          List.mem_singleton] at hmem
        rcases hmem with hmem | rfl
        · exact hprevious before hmem
        · exact ⟨error, hout⟩
      · simpa only [List.take_succ_eq_append_getElem hnext, List.getLast?_concat] using hout
      · intro it hprefix
        have hr := restore_prefix_element s it.slice i hnext hprefix
        simp only [hr]
        apply hback
        have hp := congrArg (List.take i) hprefix
        simpa only [List.take_take, Nat.min_eq_left (Nat.le_add_right i 1)] using hp
  · rename_i hdone
    change ¬i < s.val.length at hdone
    have hi' : i = s.val.length := by omega
    simp
    rw [hback ⟨s, i⟩ rfl]
    refine ⟨hwf, rfl, ?_, ?_⟩
    · simpa only [hi', List.take_length] using hprevious
    · simpa only [hi', List.take_length] using hlast
termination_by s.val.length - i

/-- Fixed-address allocation tries components in order and preserves their
    invariants. This covers every range, including empty ranges and endpoints at
    `u64::MAX`. Ending the returned mutable borrow writes back the final set. -/
@[step]
theorem allocate_at_spec (self : AddressAllocatorSet) (range : AddressRange)
    (allocation : resources.Alloc) (tag : String) (hwf : WellFormed self) :
    allocate_at self range allocation tag ⦃ result a back =>
      WellFormed a ∧ AllocationAtOutcome self range allocation tag result a ∧
      ∀ updated, back updated = updated ⦄ := by
  unfold allocate_at
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with allocate_at_loop_spec self.allocators 0 (fun it => it) range allocation tag
    .OutOfSpace (Nat.zero_le _) hwf (by simp) (by simp) (by intros; rfl)
    as ⟨result, it, hw, hout⟩
  exact ⟨hw, hout, fun _ => trivial⟩

/-- A successful lookup returns the exact range and tag from the first allocator
    containing the key. Absence means that every allocator lacks the key. -/
def GetOutcome (self : AddressAllocatorSet) (allocation : resources.Alloc)
    (found : Option (resources.address_range.AddressRange × String)) : Prop :=
  match found with
  | none => ∀ allocator ∈ self.allocators.val, AddressAllocator.GetOutcome allocator allocation none
  | some entry => ∃ before allocator after,
      self.allocators.val = before ++ allocator :: after ∧
      AddressAllocator.GetOutcome allocator allocation (some entry) ∧
      ∀ earlier ∈ before, AddressAllocator.GetOutcome earlier allocation none

-- The unvisited suffix shrinks on every unsuccessful lookup. Its first present
-- entry is unchanged when the current allocator does not contain the key.
private theorem get_loop_spec (allocators : Slice AddressAllocator) (i : Nat)
    (allocation : resources.Alloc) :
    get_loop ⟨allocators, i⟩ allocation ⦃ found =>
      found = (allocators.val.drop i).findSome?
        (fun allocator => Finmap.lookup allocation allocator.allocs) ⦄ := by
  unfold get_loop
  rw [loop.eq_def]
  simp only [get_loop.body, core.slice.iter.IteratorSliceIter.next,
    Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp only [bind_ok]
    step with AddressAllocator.get_spec allocators.val[i] allocation as ⟨found, hfound⟩
    unfold AddressAllocator.GetOutcome at hfound
    subst found
    rw [List.drop_eq_getElem_cons hnext]
    cases hlookup : Finmap.lookup allocation allocators.val[i].allocs with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true,
        ↓reduceIte, bind_ok, List.findSome?_cons, hlookup]
      exact get_loop_spec allocators (i + 1) allocation
    | some entry =>
      simp only [Option.isSome_some, ↓reduceIte, bind_ok, WP.spec_ok,
        List.findSome?_cons, hlookup]
  · rename_i hdone
    simp [List.drop_eq_nil_of_le (by omega : allocators.val.length ≤ i)]
termination_by allocators.val.length - i

/-- Total correctness of ordered lookup, including empty sets and duplicate keys
    across allocators. No allocator invariant or uniqueness assumption is needed. -/
@[step]
theorem get_spec (self : AddressAllocatorSet) (allocation : resources.Alloc) :
    get self allocation ⦃ found => GetOutcome self allocation found ⦄ := by
  unfold get
  simp only [core.slice.Slice.iter, bind_ok]
  step with get_loop_spec self.allocators 0 allocation as ⟨found, hfound⟩
  simp only [List.drop_zero] at hfound
  cases found with
  | none =>
    simpa only [GetOutcome, AddressAllocator.GetOutcome, eq_comm] using
      List.findSome?_eq_none_iff.mp hfound.symm
  | some entry =>
    simpa only [GetOutcome, AddressAllocator.GetOutcome, eq_comm] using
      List.findSome?_eq_some_iff.mp hfound.symm

/-- The first allocator whose PCI request fits supplies the address. If every
    allocator rejects the request, return the last allocator's error, or
    `OutOfSpace` for an empty set. Each component uses the single-allocator
    contract, including invalid keys, zero sizes, and bounded arithmetic. -/
def PciOffsetOutcome (self : AddressAllocatorSet) (allocation : resources.Alloc)
    (offset size : U64) (result : core.result.Result U64 resources.Error) : Prop :=
  match result with
  | .Ok address =>
    ∃ i : Fin self.allocators.val.length,
      AddressAllocator.PciOffsetOutcome self.allocators.val[i] allocation offset size (.Ok address) ∧
      ∀ j : Fin self.allocators.val.length, j < i →
        ∃ error, AddressAllocator.PciOffsetOutcome self.allocators.val[j]
          allocation offset size (.Err error)
  | .Err error =>
    (∀ i : Fin self.allocators.val.length,
      ∃ e, AddressAllocator.PciOffsetOutcome self.allocators.val[i]
        allocation offset size (.Err e)) ∧
    match self.allocators.val.getLast? with
    | none => error = .OutOfSpace
    | some allocator =>
      AddressAllocator.PciOffsetOutcome allocator allocation offset size (.Err error)

private theorem pci_offset_loop_spec (self : AddressAllocatorSet)
    (allocation : resources.Alloc) (offset size : U64) (i : Nat) (last : resources.Error)
    (hi : i ≤ self.allocators.val.length)
    (hfailed : ∀ j : Fin self.allocators.val.length, j.val < i →
      ∃ error, AddressAllocator.PciOffsetOutcome self.allocators.val[j]
        allocation offset size (.Err error))
    (hlast : if h : i = 0 then last = .OutOfSpace else
      AddressAllocator.PciOffsetOutcome (self.allocators.val[i - 1]'(by omega))
        allocation offset size (.Err last)) :
    address_from_pci_offset_loop ⟨self.allocators, i⟩ allocation offset size (.Err last)
      ⦃ result => PciOffsetOutcome self allocation offset size result ⦄ := by
  unfold address_from_pci_offset_loop
  rw [loop.eq_def]
  simp only [address_from_pci_offset_loop.body, core.slice.iter.IteratorSliceIter.next,
    Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp
    step with AddressAllocator.address_from_pci_offset_spec self.allocators.val[i]
      allocation offset size as ⟨result, houtcome⟩
    cases result with
    | Ok address =>
      simp only [core.result.Result.is_ok, bind_ok, ↓reduceIte, WP.spec_ok]
      exact ⟨⟨i, hnext⟩, houtcome, hfailed⟩
    | Err error =>
      simp only [core.result.Result.is_ok, bind_ok, Bool.false_eq_true, ↓reduceIte]
      apply pci_offset_loop_spec self allocation offset size (i + 1) error (by omega)
      · intro j hj
        by_cases he : j.val = i
        · exact ⟨error, by simpa [he] using houtcome⟩
        · exact hfailed j (by omega)
      · simpa using houtcome
  · rename_i hdone
    have he : i = self.allocators.val.length := by omega
    simp
    refine ⟨fun j => hfailed j (by omega), ?_⟩
    by_cases hz : i = 0
    · have hempty : self.allocators.val = [] := List.eq_nil_of_length_eq_zero (by omega)
      simpa [hempty] using (by simpa [hz] using hlast : last = .OutOfSpace)
    · simp only [hz, ↓reduceDIte] at hlast
      have hlastIndex : self.allocators.val.length - 1 < self.allocators.val.length := by omega
      simpa only [List.getLast?_eq_getElem?, List.getElem?_eq_getElem hlastIndex, he]
        using hlast
termination_by self.allocators.val.length - i

/-- Total correctness of ordered PCI offset lookup. No component invariant or
    uniqueness of allocation keys across the set is required. -/
@[step]
theorem address_from_pci_offset_spec (self : AddressAllocatorSet) (allocation : resources.Alloc)
    (offset size : U64) :
    address_from_pci_offset self allocation offset size ⦃ result =>
      PciOffsetOutcome self allocation offset size result ⦄ := by
  unfold address_from_pci_offset
  simp only [core.slice.Slice.iter, bind_ok]
  exact pci_offset_loop_spec self allocation offset size 0 .OutOfSpace
    (Nat.zero_le _) (by simp) (by simp)

/-- The first successful release determines the result. Earlier attempts retain
    their state changes, and later components are unchanged. If every attempt
    fails, return the last error, or `OutOfSpace` for an empty set. -/
def ReleaseOutcome (self : AddressAllocatorSet) (allocation : resources.Alloc)
    (result : core.result.Result AddressRange resources.Error)
    (updated : AddressAllocatorSet) : Prop :=
  match result with
  | .Ok range =>
    ∃ (i : Fin self.allocators.val.length) (released : AddressAllocator) (changed : List AddressAllocator),
      AddressAllocator.ReleaseOutcome self.allocators.val[i] allocation (.Ok range) released ∧
      List.Forall₂ (fun before after => ∃ error,
        AddressAllocator.ReleaseOutcome before allocation (.Err error) after)
        (self.allocators.val.take i.val) changed ∧
      updated.allocators.val = changed ++ released :: self.allocators.val.drop (i.val + 1)
  | .Err error =>
    List.Forall₂ (fun before after => ∃ e,
      AddressAllocator.ReleaseOutcome before allocation (.Err e) after)
      self.allocators.val updated.allocators.val ∧
    match self.allocators.val.getLast?, updated.allocators.val.getLast? with
    | none, none => error = .OutOfSpace
    | some before, some after =>
      AddressAllocator.ReleaseOutcome before allocation (.Err error) after
    | _, _ => False

/-- The set retains its length and each component's pools and alignments. -/
theorem ReleaseOutcome.pools_alignments {self updated allocation result}
    (h : ReleaseOutcome self allocation result updated) :
    List.Forall₂ (fun before after => after.pools = before.pools ∧
      after.min_align = before.min_align ∧ after.preferred_align = before.preferred_align)
      self.allocators.val updated.allocators.val := by
  cases result with
  | Ok range =>
    obtain ⟨i, released, changed, hlast, hfailed, hupdated⟩ := h
    rw [hupdated]
    conv_lhs =>
      rw [← List.take_append_drop i.val self.allocators.val, List.drop_eq_getElem_cons i.isLt]
    exact List.rel_append (hfailed.imp (fun _ _ ⟨_, h⟩ => h.pools_alignments))
      (.cons hlast.pools_alignments (by simp [List.forall₂_same]))
  | Err error => exact h.1.imp (fun _ _ ⟨_, h⟩ => h.pools_alignments)

/-- An absent key leaves the set unchanged, returning `BadAlloc` for a nonempty
    set and `OutOfSpace` for an empty set. -/
theorem ReleaseOutcome.missing {self updated allocation result}
    (h : ReleaseOutcome self allocation result updated)
    (hmissing : ∀ a ∈ self.allocators.val, Finmap.lookup allocation a.allocs = none) :
    updated = self ∧ result = .Err (match self.allocators.val with
      | [] => .OutOfSpace
      | _ :: _ => .BadAlloc allocation) := by
  cases result with
  | Ok range =>
    obtain ⟨i, released, changed, hlast, _, _⟩ := h
    have hm := hmissing self.allocators.val[i] (List.getElem_mem i.isLt)
    simp only [AddressAllocator.ReleaseOutcome, hm] at hlast
    cases hlast.1
  | Err error =>
    obtain ⟨hfailed, hlast⟩ := h
    have heq : self.allocators.val = updated.allocators.val := by
      have hboth := (List.forall₂_and_left _ _).mpr ⟨hmissing, hfailed⟩
      have hsame : List.Forall₂ (fun before after => before = after)
          self.allocators.val updated.allocators.val := hboth.imp (fun before after ⟨hm, _, h⟩ => by
        simp only [AddressAllocator.ReleaseOutcome, hm] at h
        exact h.2.symm)
      simpa only [List.forall₂_eq_eq_eq] using hsame
    have hset : updated = self := by
      cases self
      cases updated
      congr 1
      exact Slice.ext _ _ heq.symm
    subst updated
    refine ⟨rfl, congrArg core.result.Result.Err ?_⟩
    cases hl : self.allocators.val.getLast? with
    | none =>
      have hempty := List.getLast?_eq_none_iff.mp hl
      simpa [hl, hempty] using hlast
    | some last =>
      have hm := hmissing last (List.mem_of_getLast? hl)
      simp only [hl, AddressAllocator.ReleaseOutcome, hm, core.result.Result.Err.injEq] at hlast
      rw [hlast.1]
      cases he : self.allocators.val with
      | nil => simp [he] at hl
      | cons => rfl

/-- `changed` records the failed prefix. Pending mutable borrows write that
    prefix back while preserving the remaining slice supplied by the loop. -/
private theorem release_loop_spec (s : Slice AddressAllocator) (i : Nat)
    (back : core.slice.iter.IterMut AddressAllocator → core.slice.iter.IterMut AddressAllocator)
    (allocation : resources.Alloc) (lastError : resources.Error)
    (changed : List AddressAllocator) (hi : i ≤ s.val.length)
    (hwf : ∀ a ∈ s.val, AddressAllocator.WellFormed a)
    (hwfc : ∀ a ∈ changed, AddressAllocator.WellFormed a)
    (hfailed : List.Forall₂ (fun before after => ∃ error,
      AddressAllocator.ReleaseOutcome before allocation (.Err error) after) (s.val.take i) changed)
    (hlast : match (s.val.take i).getLast?, changed.getLast? with
      | none, none => lastError = .OutOfSpace
      | some before, some after => AddressAllocator.ReleaseOutcome before allocation (.Err lastError) after
      | _, _ => False)
    (hback : ∀ final : core.slice.iter.IterMut AddressAllocator,
      final.slice.val.length = s.val.length →
      (back final).slice.val = changed ++ final.slice.val.drop i) :
    release_loop ⟨s, i⟩ back allocation (.Err lastError) ⦃ result final =>
      WellFormed ⟨final.slice⟩ ∧ ReleaseOutcome ⟨s⟩ allocation result ⟨final.slice⟩ ⦄ := by
  unfold release_loop
  rw [loop.eq_def]
  simp only [release_loop.body, core.slice.iter.IteratorIterMut.next, Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp
    step with AddressAllocator.release_spec s.val[i] allocation
      (hwf _ (List.getElem_mem hnext)) as ⟨pair, hwfa, houtcome⟩
    rcases pair with ⟨result, a⟩
    dsimp only at hwfa houtcome
    have hwrite (final : core.slice.iter.IterMut AddressAllocator)
        (hlen : final.slice.val.length = s.val.length) :
        (back { final with slice := final.slice.setAtNat i a }).slice.val =
          changed ++ a :: final.slice.val.drop (i + 1) := by
      rw [hback _ (by simpa [Slice.setAtNat] using hlen)]
      simp only [Slice.setAtNat, Slice.from_val, List.drop_set, Nat.lt_irrefl,
        ↓reduceIte, Nat.sub_self]
      rw [List.drop_eq_getElem_cons (by omega : i < final.slice.val.length)]
      rfl
    cases result with
    | Ok range =>
      simp [core.result.Result.is_ok]
      constructor
      · intro b hb
        rw [hwrite ⟨s, i + 1⟩ rfl] at hb
        simp only [List.mem_append, List.mem_cons] at hb
        rcases hb with hb | rfl | hb
        · exact hwfc b hb
        · exact hwfa
        · exact hwf b (List.mem_of_mem_drop hb)
      · exact ⟨⟨i, hnext⟩, a, changed, houtcome, hfailed, hwrite ⟨s, i + 1⟩ rfl⟩
    | Err error =>
      simp [core.result.Result.is_ok]
      apply release_loop_spec s (i + 1)
        (fun final => back { final with slice := final.slice.setAtNat i a })
        allocation error (changed ++ [a]) (by omega) hwf
      · intro b hb
        simp only [List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact hwfc b hb
        · exact hwfa
      · rw [List.take_succ_eq_append_getElem hnext]
        exact List.rel_append hfailed (.cons ⟨error, houtcome⟩ .nil)
      · rw [List.take_succ_eq_append_getElem hnext]
        simpa only [List.getLast?_append, List.getLast?_singleton, Option.or] using houtcome
      · intro final hlen
        simpa only [List.append_assoc, List.singleton_append] using hwrite final hlen
  · rename_i hdone
    have he : i = s.val.length := by omega
    have hwrite : (back ⟨s, i⟩).slice.val = changed := by
      simpa only [he, List.drop_length, List.append_nil] using hback ⟨s, i⟩ rfl
    simp
    constructor
    · simpa only [WellFormed, hwrite] using hwfc
    · unfold ReleaseOutcome
      dsimp only
      rw [hwrite]
      constructor
      · simpa only [he, List.take_length] using hfailed
      · simp only [he, List.take_length] at hlast
        cases hbefore : s.val.getLast? <;> cases hafter : changed.getLast? <;> simp_all only
termination_by s.val.length - i

/-- Release searches in slice order, preserves component invariants, and writes
    back all attempted releases. The returned mutable borrow is the identity. -/
@[step]
theorem release_spec (self : AddressAllocatorSet) (allocation : resources.Alloc)
    (hwf : WellFormed self) :
    release self allocation ⦃ result updated back =>
      ReleaseOutcome self allocation result updated ∧ WellFormed updated ∧
      ∀ final, back final = final ⦄ := by
  unfold release
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with release_loop_spec self.allocators 0 (fun it => it) allocation .OutOfSpace []
    (by omega) hwf (by simp) (by simp) (by simp) (by simp)
    as ⟨result, final, hwfa, houtcome⟩
  exact ⟨houtcome, hwfa, by simp⟩

end resources.address_allocator.AddressAllocatorSet
