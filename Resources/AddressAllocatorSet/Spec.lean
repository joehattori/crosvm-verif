module
public import Resources.AddressAllocator.Spec
@[expose] public section
set_option maxRecDepth 2048
open Aeneas Aeneas.Std Result
open resources.address_allocator

namespace resources.address_allocator.AddressAllocatorSet

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
    (hwf : ∀ a ∈ self.allocators.val, AddressAllocator.WellFormed a) :
    ∀ a ∈ updated.allocators.val, AddressAllocator.WellFormed a := by
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
    (hi : i ≤ s.val.length) (hwf : ∀ a ∈ s.val, AddressAllocator.WellFormed a)
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
    (allocation : resources.Alloc) (tag : String)
    (hwf : ∀ a ∈ self.allocators.val, AddressAllocator.WellFormed a) :
    allocate self size allocation tag ⦃ result updated back =>
      AllocationOutcome self size allocation tag result updated ∧
      (∀ a ∈ updated.allocators.val, AddressAllocator.WellFormed a) ∧
      ∀ final, back final = final ⦄ := by
  unfold allocate
  simp only [core.slice.Slice.iter_mut, bind_ok]
  step with allocate_loop_spec self.allocators 0 (fun it => it) size allocation tag .OutOfSpace
    (by omega) hwf (by simp) (by simp) as ⟨result, final, rest, hprefix, houtcome⟩
  simpa only [implies_true, and_true] using
    And.intro houtcome (houtcome.wellFormed hwf)

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

end resources.address_allocator.AddressAllocatorSet
