module
public import Resources.Funs
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

end resources.address_allocator.AddressAllocatorSet
