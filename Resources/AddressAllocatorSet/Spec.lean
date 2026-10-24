module
public import Resources.AddressAllocator.Spec
@[expose] public section
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
