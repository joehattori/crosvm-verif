module
public import VmMemory.Funs
public import Utils.Alignment
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address
open Utils.Alignment

namespace vm_memory.guest_address.GuestAddress

def OffsetFromOutcome (self base : GuestAddress) (result : U64) : Prop :=
  result.val = self.val - base.val

def CmpOutcome (self other : GuestAddress) (result : Ordering) : Prop :=
  (result = .lt ↔ self.val < other.val) ∧
  (result = .eq ↔ self.val = other.val) ∧
  (result = .gt ↔ other.val < self.val)

def PartialCmpOutcome (self other : GuestAddress) (result : Option Ordering) : Prop :=
  ∃ order, result = some order ∧ CmpOutcome self other order

def AlignDownOutcome (self : GuestAddress) (alignment : U64) (result : GuestAddress) : Prop :=
  if alignment.val ≤ 1 then result = self
  else ∃ mask : U64, mask.val = alignment.val - 1 ∧ result = self &&& ~~~mask

def AlignOutcome (self : GuestAddress) (alignment : U64) (result : Option GuestAddress) : Prop :=
  if alignment.val ≤ 1 then result = some self
  else ∃ mask : U64, mask.val = alignment.val - 1 ∧
    result = (U64.checked_add self mask).map (fun added => added &&& ~~~mask)

theorem AlignOutcome.le_one_iff (self : GuestAddress) (alignment : U64)
    (result : Option GuestAddress) (h : alignment.val ≤ 1) :
    AlignOutcome self alignment result ↔ result = some self := by
  simp [AlignOutcome, h]

/-- For zero or power-of-two alignment, the bitwise contract is mathematical rounding down. -/
theorem AlignDownOutcome.iff_alignDown (self : GuestAddress) (alignment : U64)
    (result : GuestAddress) (ha : alignment.val = 0 ∨ alignment.val.isPowerOfTwo) :
    AlignDownOutcome self alignment result ↔
      result.val = alignDown self.val (max alignment.val 1) := by
  by_cases h : alignment.val ≤ 1
  · simp [AlignDownOutcome, h, alignDown, Nat.mod_one]
    scalar_tac
  · have hp : alignment.val.isPowerOfTwo := ha.resolve_left (by omega)
    simp only [AlignDownOutcome, if_neg h, Nat.max_eq_left (by omega : 1 ≤ alignment.val)]
    constructor
    · rintro ⟨mask, hm, rfl⟩
      exact mask_alignDown self alignment mask hp hm
    · intro hr
      let mask := U64.ofNatCore (alignment.val - 1) (by have := alignment.hBounds; omega)
      have hm : mask.val = alignment.val - 1 := by simp [mask]
      exact ⟨mask, hm, UScalar.eq_of_val_eq
        (hr.trans (mask_alignDown self alignment mask hp hm).symm)⟩

/-- The checked-add-and-mask contract is equivalent to rounding up, including overflow. -/
theorem AlignOutcome.iff_alignUp (self : GuestAddress) (alignment : U64)
    (result : Option GuestAddress) (ha : alignment.val = 0 ∨ alignment.val.isPowerOfTwo) :
    AlignOutcome self alignment result ↔
      match result with
      | some r => r.val = alignUp self.val (max alignment.val 1)
      | none => U64.max < alignUp self.val (max alignment.val 1) := by
  by_cases h : alignment.val ≤ 1
  · cases result <;>
      simp [AlignOutcome, h, alignUp, Nat.mod_one] <;> scalar_tac
  · have hp : alignment.val.isPowerOfTwo := ha.resolve_left (by omega)
    let mask := U64.ofNatCore (alignment.val - 1) (by have := alignment.hBounds; omega)
    have hm : mask.val = alignment.val - 1 := by simp [mask]
    have heq : AlignOutcome self alignment result ↔
        result = (U64.checked_add self mask).map (fun added => added &&& ~~~mask) := by
      simp only [AlignOutcome, if_neg h]
      constructor
      · rintro ⟨mask', hm', hr⟩
        have he : mask' = mask := UScalar.eq_of_val_eq (hm'.trans hm.symm)
        simpa only [he] using hr
      · exact fun hr => ⟨mask, hm, hr⟩
    rw [heq, ← Option.map_inj_right (fun x y h => UScalar.eq_of_val_eq h)]
    simp only [Option.map_map, Function.comp_def]
    rw [checked_add_mask_alignUp self alignment mask hp hm]
    cases result <;>
      simp only [Option.map_none, Option.map_some,
        Nat.max_eq_left (by omega : 1 ≤ alignment.val)] <;>
      split_ifs <;> simp_all
    scalar_tac

@[step]
theorem constructor_spec (addr : U64) :
    GuestAddress.constructor addr ⦃ r => r = addr ⦄ := by
  simp [GuestAddress.constructor]

@[step]
theorem clone_spec (self : GuestAddress) :
    Insts.CoreCloneClone.clone self ⦃ r => r = self ⦄ := by
  simp [Insts.CoreCloneClone.clone]

/-- Subtraction is exact when the base does not exceed the address. -/
@[step]
theorem offset_from_spec (self base : GuestAddress) (h : base.val ≤ self.val) :
    GuestAddress.offset_from self base ⦃ r => OffsetFromOutcome self base r ⦄ := by
  unfold GuestAddress.offset_from OffsetFromOutcome
  step
  omega

/-- Unlike checked_sub, an invalid offset subtraction fails in Aeneas's Result. -/
theorem offset_from_underflow (self base : GuestAddress) (h : self.val < base.val) :
    GuestAddress.offset_from self base = fail .integerOverflow := by
  change UScalar.sub self base = _
  simp [UScalar.sub, h]

@[step]
theorem offset_spec (self : GuestAddress) :
    GuestAddress.offset self ⦃ r => r = self ⦄ := by
  simp [GuestAddress.offset]

@[step]
theorem checked_add_spec (self : GuestAddress) (other : U64) :
    GuestAddress.checked_add self other ⦃ result => result = U64.checked_add self other ⦄ := by
  unfold GuestAddress.checked_add
  cases U64.checked_add self other <;>
    simp [core.option.Option.map,
      P.Insts.CoreOpsFunctionFnOnceTupleU64GuestAddress.call_once, GuestAddress.constructor, lift]

/-- Despite its name, unchecked_add uses Rust's wrapping arithmetic on all inputs. -/
@[step]
theorem unchecked_add_spec (self : GuestAddress) (offset : U64) :
    GuestAddress.unchecked_add self offset ⦃ r => r = U64.wrapping_add self offset ⦄ := by
  simp [GuestAddress.unchecked_add, lift, U64.wrapping_add, core.num.U64.wrapping_add]

theorem unchecked_add_no_overflow_spec (self : GuestAddress) (offset : U64)
    (h : self.val + offset.val ≤ U64.max) :
    GuestAddress.unchecked_add self offset ⦃ r => r.val = self.val + offset.val ⦄ := by
  step as ⟨r, hr⟩
  rw [hr, U64.wrapping_add_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

@[step]
theorem checked_sub_spec (self : GuestAddress) (other : U64) :
    GuestAddress.checked_sub self other ⦃ result => result = U64.checked_sub self other ⦄ := by
  unfold GuestAddress.checked_sub
  cases U64.checked_sub self other <;>
    simp [core.option.Option.map,
      P.Insts.CoreOpsFunctionFnOnceTupleU64GuestAddress.call_once, GuestAddress.constructor, lift]

@[step]
theorem mask_spec (self : GuestAddress) (mask : U64) :
    GuestAddress.mask self mask ⦃ r => r = self &&& mask ⦄ := by
  simp [GuestAddress.mask, lift]

@[step]
theorem bitand_spec (self : GuestAddress) (other : U64) :
    Insts.CoreOpsBitBitAndU64GuestAddress.bitand self other ⦃ r => r = self &&& other ⦄ := by
  simp [Insts.CoreOpsBitBitAndU64GuestAddress.bitand, lift]

@[step]
theorem bitor_spec (self : GuestAddress) (other : U64) :
    Insts.CoreOpsBitBitOrU64GuestAddress.bitor self other ⦃ r => r = self ||| other ⦄ := by
  simp [Insts.CoreOpsBitBitOrU64GuestAddress.bitor, lift]

@[step]
theorem eq_spec (self other : GuestAddress) :
    Insts.CoreCmpPartialEqGuestAddress.eq self other ⦃ b => b = true ↔ self.val = other.val ⦄ := by
  simp [Insts.CoreCmpPartialEqGuestAddress.eq]
  scalar_tac

@[step]
theorem cmp_spec (self other : GuestAddress) :
    Insts.CoreCmpOrd.cmp self other ⦃ o => CmpOutcome self other o ⦄ := by
  simp [Insts.CoreCmpOrd.cmp, CmpOutcome, core.cmp.impls.OrdU64.cmp, compare, compareOfLessAndEq]
  split_ifs <;> simp_all <;> scalar_tac

@[step]
theorem partial_cmp_spec (self other : GuestAddress) :
    Insts.CoreCmpPartialOrdGuestAddress.partial_cmp self other ⦃ o => PartialCmpOutcome self other o ⦄ := by
  unfold Insts.CoreCmpPartialOrdGuestAddress.partial_cmp
  step as ⟨o, ho⟩
  exact ⟨o, rfl, ho⟩

/-- The inherited comparisons used by MemoryRegion agree with address order. -/
@[step]
theorem lt_spec (self other : GuestAddress) :
    core.cmp.PartialOrd.lt.trait_default Insts.CoreCmpPartialOrdGuestAddress self other
      ⦃ b => b = true ↔ self.val < other.val ⦄ := by
  unfold core.cmp.PartialOrd.lt.trait_default core.cmp.PartialOrd.lt.default
    core.cmp.PartialOrd.lt_body
  step as ⟨o, h⟩
  obtain ⟨order, ho, horder⟩ := h
  simp [ho, CmpOutcome] at horder ⊢
  exact horder.1

@[step]
theorem le_spec (self other : GuestAddress) :
    core.cmp.PartialOrd.le.trait_default Insts.CoreCmpPartialOrdGuestAddress self other
      ⦃ b => b = true ↔ self.val ≤ other.val ⦄ := by
  unfold core.cmp.PartialOrd.le.trait_default core.cmp.PartialOrd.le.default
    core.cmp.PartialOrd.le_body
  step as ⟨o, h⟩
  obtain ⟨order, ho, horder⟩ := h
  simp [ho, CmpOutcome] at horder ⊢
  rw [horder.1, horder.2.1]
  omega

@[step]
theorem ge_spec (self other : GuestAddress) :
    core.cmp.PartialOrd.ge.trait_default Insts.CoreCmpPartialOrdGuestAddress self other
      ⦃ b => b = true ↔ other.val ≤ self.val ⦄ := by
  unfold core.cmp.PartialOrd.ge.trait_default core.cmp.PartialOrd.ge.default
    core.cmp.PartialOrd.ge_body
  step as ⟨o, h⟩
  obtain ⟨order, ho, horder⟩ := h
  simp [ho, CmpOutcome] at horder ⊢
  rw [horder.2.2, horder.2.1]
  omega

/-- Exact bitwise behavior, including the identity branch for zero and one. -/
@[step]
theorem align_down_spec (self : GuestAddress) (alignment : U64) :
    GuestAddress.align_down self alignment ⦃ r => AlignDownOutcome self alignment r ⦄ := by
  unfold GuestAddress.align_down AlignDownOutcome
  split
  · have h : alignment.val ≤ 1 := by scalar_tac
    simp [h]
  · have h : ¬alignment.val ≤ 1 := by scalar_tac
    simp only [if_neg h]
    step as ⟨mask, hm⟩
    simp only [lift, bind_ok]
    step as ⟨r, hr⟩
    exact ⟨mask, by omega, hr⟩

private theorem align_closure_spec (alignment : U64) (self : GuestAddress) (mask : U64)
    (ha : 1 < alignment.val) (hm : mask.val = alignment.val - 1) :
    align.closure.Insts.CoreOpsFunctionFnOnceTupleGuestAddressGuestAddress.call_once
      alignment self ⦃ r => r = self &&& ~~~mask ⦄ := by
  unfold align.closure.Insts.CoreOpsFunctionFnOnceTupleGuestAddressGuestAddress.call_once
  step as ⟨actualMask, hm'⟩
  have he : actualMask = mask := by scalar_tac
  simp only [lift, bind_ok, he]
  step
  assumption

/-- Exact checked-add-and-mask behavior, including the identity branch for zero and one. -/
@[step]
theorem align_spec (self : GuestAddress) (alignment : U64) :
    GuestAddress.align self alignment ⦃ result => AlignOutcome self alignment result ⦄ := by
  unfold GuestAddress.align AlignOutcome
  split
  · have h : alignment.val ≤ 1 := by scalar_tac
    simp [h]
  · have h : 1 < alignment.val := by scalar_tac
    simp only [if_neg (by omega : ¬alignment.val ≤ 1)]
    step as ⟨mask, hm⟩
    have hmask : mask.val = alignment.val - 1 := by omega
    step as ⟨result, he⟩
    cases result with
    | none =>
      simp only [core.option.Option.map_none, WP.spec_ok]
      exact ⟨mask, hmask, by rw [← he]; rfl⟩
    | some added =>
      simp only [core.option.Option.map_some]
      step with align_closure_spec alignment added mask h hmask as ⟨r, hbits⟩
      exact ⟨mask, hmask, by rw [← he]; simp [hbits]⟩

end vm_memory.guest_address.GuestAddress
