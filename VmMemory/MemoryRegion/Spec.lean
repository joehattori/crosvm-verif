module
public import VmMemory.GuestAddress.Spec
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address

namespace vm_memory.guest_memory.MemoryRegion

/-- The exclusive end of a region is representable as a guest address. -/
def ValidBounds (self : MemoryRegion) : Prop :=
  self.guest_base.val + self.mapping.length.val ≤ U64.max

/-- The exact endpoint computed by Rust's unchecked_add, including wraparound. -/
def EndOutcome (self : MemoryRegion) (result : GuestAddress) : Prop :=
  result = U64.wrapping_add self.guest_base (UScalar.cast .U64 self.mapping.length)

theorem EndOutcome.exists (self : MemoryRegion) :
    ∃ result, EndOutcome self result :=
  ⟨_, rfl⟩

private theorem length_cast_val (length : Usize) :
    (UScalar.cast .U64 length).val = length.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

/-- Under valid bounds, the wrapping endpoint is the mathematical exclusive end. -/
theorem EndOutcome.val_eq_of_valid {self : MemoryRegion} {result : GuestAddress}
    (he : EndOutcome self result) (h : ValidBounds self) :
    result.val = self.guest_base.val + self.mapping.length.val := by
  rw [he, U64.wrapping_add_val_eq, length_cast_val]
  apply Nat.mod_eq_of_lt
  unfold ValidBounds at h
  scalar_tac

@[step]
theorem start_spec (self : MemoryRegion) :
    self.start ⦃ r => r = self.guest_base ⦄ := by
  simp [MemoryRegion.start]

/-- Exact behavior even when the exclusive end wraps around the address space. -/
@[step]
theorem end_spec (self : MemoryRegion) :
    self.end ⦃ r => EndOutcome self r ⦄ := by
  unfold MemoryRegion.end
  simp only [base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, bind_ok, lift]
  step as ⟨r, hr⟩
  exact hr

/-- The end is exclusive; the bound excludes a mathematical end of 2^64. -/
theorem end_no_overflow_spec (self : MemoryRegion) (h : ValidBounds self) :
    self.end ⦃ r => r.val = self.guest_base.val + self.mapping.length.val ⦄ := by
  step as ⟨r, hr⟩
  exact hr.val_eq_of_valid h

/-- Membership uses the endpoint specified by EndOutcome, even if it wraps. -/
@[step]
theorem contains_spec (self : MemoryRegion) (addr : GuestAddress) :
    self.contains addr ⦃ b =>
      ∃ endAddr, EndOutcome self endAddr ∧
        (b = true ↔ self.guest_base.val ≤ addr.val ∧ addr.val < endAddr.val) ⦄ := by
  unfold MemoryRegion.contains
  step as ⟨b, hb⟩
  split
  · step as ⟨endAddr, he⟩
    step as ⟨result, hr⟩
    refine ⟨endAddr, he, ?_⟩
    simp_all
  · obtain ⟨endAddr, he⟩ := EndOutcome.exists self
    simp only [WP.spec_ok]
    refine ⟨endAddr, he, ?_⟩
    simp_all

/-- Checked-add overflow returns false; otherwise compare the checked request
    end with the region endpoint specified by EndOutcome. -/
@[step]
theorem contains_range_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64) :
    self.contains_range addr size ⦃ b =>
      match U64.checked_add addr size with
      | none => b = false
      | some endAddr =>
        ∃ regionEnd, EndOutcome self regionEnd ∧
          (b = true ↔ self.guest_base.val ≤ addr.val ∧
            endAddr.val ≤ regionEnd.val) ⦄ := by
  unfold MemoryRegion.contains_range
  step as ⟨o, ho⟩
  rw [← ho]
  cases o with
  | none => simp
  | some endAddr =>
    step as ⟨b, hb⟩
    split
    · step as ⟨regionEnd, he⟩
      step as ⟨result, hr⟩
      refine ⟨regionEnd, he, ?_⟩
      simp_all
    · obtain ⟨regionEnd, he⟩ := EndOutcome.exists self
      simp only [WP.spec_ok]
      refine ⟨regionEnd, he, ?_⟩
      simp_all

/-- Valid bounds recover membership in the mathematical half-open interval. -/
theorem contains_no_overflow_spec (self : MemoryRegion) (addr : GuestAddress)
    (h : ValidBounds self) :
    self.contains addr ⦃ b =>
      b = true ↔ self.guest_base.val ≤ addr.val ∧
        addr.val < self.guest_base.val + self.mapping.length.val ⦄ := by
  apply WP.spec_mono (contains_spec self addr)
  rintro b ⟨endAddr, he, hb⟩
  rwa [he.val_eq_of_valid h] at hb

/-- Valid bounds recover mathematical containment, including empty requests. -/
theorem contains_range_no_overflow_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64)
    (h : ValidBounds self) :
    self.contains_range addr size ⦃ b =>
      b = true ↔ self.guest_base.val ≤ addr.val ∧
        addr.val + size.val ≤ self.guest_base.val + self.mapping.length.val ⦄ := by
  apply WP.spec_mono (contains_range_spec self addr size)
  intro b hb
  have hAdd := U64.checked_add_bv_spec addr size
  cases ho : U64.checked_add addr size with
  | none =>
    simp only [ho] at hb hAdd
    simp only [hb, Bool.false_eq_true, false_iff, not_and]
    intro _ hFit
    exact Nat.not_le_of_gt hAdd (hFit.trans h)
  | some endAddr =>
    simp only [ho] at hb hAdd
    obtain ⟨regionEnd, he, hb⟩ := hb
    rwa [he.val_eq_of_valid h, hAdd.2.1] at hb

/-- Zero-length regions contain no individual address, including their start. -/
theorem contains_empty_spec (self : MemoryRegion) (addr : GuestAddress)
    (hEmpty : self.mapping.length.val = 0) :
    self.contains addr ⦃ b => b = false ⦄ := by
  have h : ValidBounds self := by
    simp only [ValidBounds, hEmpty, Nat.add_zero]
    scalar_tac
  apply WP.spec_mono (contains_no_overflow_spec self addr h)
  intro b hb
  simp [hEmpty] at hb
  cases b <;> simp_all
  omega

/-- An empty request at the exclusive end is accepted, even for an empty region. -/
theorem contains_range_empty_at_end_spec (self : MemoryRegion) (addr : GuestAddress)
    (h : ValidBounds self)
    (hEnd : addr.val = self.guest_base.val + self.mapping.length.val) :
    self.contains_range addr 0#u64 ⦃ b => b = true ⦄ := by
  apply WP.spec_mono (contains_range_no_overflow_spec self addr 0#u64 h)
  intro b hb
  apply hb.mpr
  simp [hEnd]

/-- Query overflow returns false regardless of the region's own bounds. -/
theorem contains_range_overflow_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64)
    (hOverflow : U64.max < addr.val + size.val) :
    self.contains_range addr size ⦃ b => b = false ⦄ := by
  apply WP.spec_mono (contains_range_spec self addr size)
  intro b hb
  have hAdd := U64.checked_add_bv_spec addr size
  cases ho : U64.checked_add addr size with
  | none => simpa only [ho] using hb
  | some endAddr =>
    simp only [ho] at hAdd
    omega

end vm_memory.guest_memory.MemoryRegion
