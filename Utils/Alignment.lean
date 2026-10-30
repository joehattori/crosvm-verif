module
public import Aeneas
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std

namespace Utils.Alignment

/-- Round down to an alignment boundary, using unbounded arithmetic.
    `mask_alignDown` relates this to `addr & !(alignment - 1)` for powers of two. -/
def alignDown (addr alignment : Nat) : Nat := addr - addr % alignment

/-- Round up to an alignment boundary, using unbounded arithmetic.
    `checked_add_mask_alignUp` relates this to checked addition followed by masking. -/
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

/-- Clearing the low bits of a power-of-two alignment is mathematical rounding down.
    `hm` identifies the mask produced by Rust's `alignment - 1`. -/
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

theorem round_up_eq (x a : Nat) (ha : 0 < a) :
    alignDown (x + (a - 1)) a = alignUp x a := by
  have hr := Nat.mod_lt x ha
  have hamod : (a - 1) % a = a - 1 := Nat.mod_eq_of_lt (by omega)
  by_cases h : x % a = 0
  · simp [alignDown, alignUp, Nat.add_mod, h, hamod]
  · have hm : (x + (a - 1)) % a = x % a - 1 := by
      rw [Nat.add_mod, hamod]
      have he : x % a + (a - 1) = a + (x % a - 1) := by omega
      rw [he, Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
    simp only [alignDown, alignUp, h, ↓reduceIte, hm]
    omega

/-- A power-of-two boundary divides the u64 address-space size. -/
theorem max_mod_alignment (alignment : U64) (ha : alignment.val.isPowerOfTwo) :
    U64.max % alignment.val = alignment.val - 1 := by
  have hpos := Nat.pos_of_isPowerOfTwo ha
  obtain ⟨k, hk⟩ := ha
  have hk64 : k < 64 := by
    apply (Nat.pow_lt_pow_iff_right (by omega : 1 < 2)).mp
    rw [← hk]
    exact alignment.hBounds
  have hd : alignment.val ∣ U64.max + 1 := by
    rw [hk, U64.max_eq]
    change 2 ^ k ∣ 2 ^ 64
    exact Nat.pow_dvd_pow 2 (by omega)
  have hz := Nat.mod_eq_zero_of_dvd hd
  have hr := Nat.mod_lt U64.max hpos
  by_cases h1 : alignment.val = 1
  · simp [h1, Nat.mod_one]
  · rw [Nat.add_mod, Nat.mod_eq_of_lt (by omega : 1 < alignment.val)] at hz
    have hle : U64.max % alignment.val + 1 ≤ alignment.val := by omega
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · rw [Nat.mod_eq_of_lt hlt] at hz
      omega
    · omega

/-- For power-of-two alignments, the padded sum fits exactly when the rounded address fits. -/
theorem alignUp_le_max_iff (x alignment : U64) (ha : alignment.val.isPowerOfTwo) :
    alignUp x.val alignment.val ≤ U64.max ↔ x.val + (alignment.val - 1) ≤ U64.max := by
  have hpos := Nat.pos_of_isPowerOfTwo ha
  constructor
  · intro hle
    have hdown := le_alignDown (alignUp_mod x.val alignment.val hpos) hle
    have hup := le_alignUp x.val alignment.val
    have hbound : alignment.val ≤ U64.max := by scalar_tac
    simp only [alignDown, max_mod_alignment alignment ha] at hdown
    omega
  · intro hle
    rw [← round_up_eq _ _ hpos]
    exact (alignDown_le _ _).trans hle

/-- The checked-add-and-mask expression returns the rounded address, or `None` exactly
    when that address exceeds `u64::MAX`. `hm` represents Rust's `alignment - 1`. -/
theorem checked_add_mask_alignUp  (x alignment mask : U64)
    (ha : alignment.val.isPowerOfTwo) (hm : mask.val = alignment.val - 1) :
    (U64.checked_add x mask).map (fun added => (added &&& ~~~mask).val) =
      if alignUp x.val alignment.val ≤ U64.max
      then some (alignUp x.val alignment.val) else none := by
  have h := U64.checked_add_bv_spec x mask
  have hfit := alignUp_le_max_iff x alignment ha
  cases he : U64.checked_add x mask with
  | none =>
    simp only [he] at h
    have hn : ¬alignUp x.val alignment.val ≤ U64.max := by
      intro hle
      have := hfit.mp hle
      omega
    simp [hn]
  | some added =>
    simp only [he] at h
    have hle : alignUp x.val alignment.val ≤ U64.max := by
      apply hfit.mpr
      simpa only [hm] using h.1
    simp only [Option.map_some, ite_eq_left hle, Option.some.injEq]
    rw [mask_alignDown added alignment mask ha hm, h.2.1, hm,
      round_up_eq _ _ (Nat.pos_of_isPowerOfTwo ha)]

end Utils.Alignment
