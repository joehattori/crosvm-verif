module
public import Aeneas
public import Resources.Types
public import Resources.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
open resources.address_range

namespace resources.address_range.AddressRange

/-- Mathematical model of when an `AddressRange` is empty (`end < start`). -/
abbrev isEmptyModel (r : AddressRange) : Prop :=
  r.end.val < r.start.val

/-- Mathematical membership predicate (`start ≤ a ≤ end`). -/
abbrev containsModel (r : AddressRange) (a : Nat) : Prop :=
  r.start.val ≤ a ∧ a ≤ r.end.val

/-- Inclusive length in unbounded arithmetic; empty ranges have length zero. -/
def lenModel (r : AddressRange) : Nat :=
  if r.isEmptyModel then 0 else r.end.val - r.start.val + 1

/-- A range is nonempty exactly when it contains an address. -/
theorem not_isEmptyModel_iff_exists_containsModel (r : AddressRange) :
    ¬r.isEmptyModel ↔ ∃ addr, r.containsModel addr := by
  simp only [isEmptyModel, containsModel]
  constructor
  · intro h
    exact ⟨r.start.val, by omega⟩
  · rintro ⟨addr, h⟩
    omega

@[step]
theorem from_start_and_end_spec (s e : U64) :
    AddressRange.from_start_and_end s e ⦃ r => r.start = s ∧ r.end = e ⦄ := by
  unfold AddressRange.from_start_and_end
  simp

@[step]
theorem empty_spec :
    AddressRange.empty ⦃ r => r.start = 1#u64 ∧ r.end = 0#u64 ∧ r.isEmptyModel ⦄ := by
  unfold AddressRange.empty
  simp

@[step]
theorem is_empty_spec (r : AddressRange) :
    AddressRange.is_empty r ⦃ b => b = true ↔ r.isEmptyModel ⦄ := by
  unfold AddressRange.is_empty
  simp

@[step]
theorem contains_spec (r : AddressRange) (addr : U64) :
    AddressRange.contains r addr ⦃ b => b = true ↔ r.containsModel addr.val ⦄ := by
  unfold AddressRange.contains
  split <;> simp <;> scalar_tac

@[step]
theorem contains_range_spec (self other : AddressRange) :
    AddressRange.contains_range self other ⦃ b =>
      b = true ↔ (¬other.isEmptyModel ∧ self.start.val ≤ other.start.val ∧ other.end.val ≤ self.end.val) ⦄ := by
  unfold AddressRange.contains_range
  step
  split
  · simp_all
  · split <;> simp_all

/-- `from_start_and_size` never panics for any `start` and `size` inputs:
    - If `size = 0`, it returns `some empty`.
    - If `start + (size - 1) ≤ U64.MAX`, it returns `some [start, start + size - 1]`.
    - If `start + (size - 1) > U64.MAX`, it returns `none`. -/
@[step]
theorem from_start_and_size_spec (start size : U64) :
    AddressRange.from_start_and_size start size ⦃ opt =>
      if size.val = 0 then
        ∃ r, opt = some r ∧ r.isEmptyModel
      else if start.val + (size.val - 1) ≤ U64.max then
        ∃ r, opt = some r ∧ r.start = start ∧ r.end.val = start.val + (size.val - 1) ∧ ¬r.isEmptyModel
      else
        opt = none ⦄ := by
  unfold AddressRange.from_start_and_size
  split
  · step
    simp_all
  · step
    step
    split <;> simp_all

@[step]
theorem u64_max_spec (x y : U64) :
    core.cmp.max core.cmp.OrdU64 x y ⦃ r => r.val = max x.val y.val ⦄ := by
  simp [core.cmp.max, liftFun2]

@[step]
theorem u64_min_spec (x y : U64) :
    core.cmp.min core.cmp.OrdU64 x y ⦃ r => r.val = min x.val y.val ⦄ := by
  simp [core.cmp.min, liftFun2]

/-- The intersection contains exactly the addresses shared by both input ranges. -/
@[step]
theorem intersect_spec (self other : AddressRange) :
    AddressRange.intersect self other ⦃ r =>
      ∀ addr, r.containsModel addr ↔
        self.containsModel addr ∧ other.containsModel addr ⦄ := by
  unfold AddressRange.intersect
  step
  step
  simp_all [containsModel]
  omega

/-- Two ranges overlap exactly when they share an address. -/
@[step]
theorem overlaps_spec (self other : AddressRange) :
    AddressRange.overlaps self other ⦃ b =>
      b = true ↔ ∃ addr, self.containsModel addr ∧ other.containsModel addr ⦄ := by
  unfold AddressRange.overlaps
  step as ⟨r, hr⟩
  step
  have h_nonempty := not_isEmptyModel_iff_exists_containsModel r
  simp_all

/-- Internal endpoint characterization, including the safety of the unchecked arithmetic. -/
private theorem non_overlapping_ranges_bounds_spec (self other : AddressRange) :
    AddressRange.non_overlapping_ranges self other ⦃ before after =>
      if other.isEmptyModel then before = self ∧ after.isEmptyModel
      else (if self.start.val ≥ other.start.val then
        before.isEmptyModel
      else
        before.start.val = self.start.val ∧
        before.end.val = min (other.start.val - 1) self.end.val) ∧
      (if self.end.val ≤ other.end.val then
        after.isEmptyModel
      else
        after.start.val = max (other.end.val + 1) self.start.val ∧
        after.end.val = self.end.val) ⦄ := by
  unfold AddressRange.non_overlapping_ranges
  step with is_empty_spec other as ⟨empty, he⟩
  split
  · step
    simp_all
  · simp_all only
    split
    · step
      split
      · step
        simp_all
      · step
        step
        step
        step
        simp_all
        split_ifs <;> omega
    · step
      step
      step
      step
      split
      · step
        simp_all
        split_ifs <;> omega
      · step
        step
        step
        step
        simp_all
        split_ifs <;> omega

/-- `non_overlapping_ranges` succeeds and returns disjoint remainders containing
    exactly the addresses in `self` but not in `other`, even for empty inputs. -/
@[step]
theorem non_overlapping_ranges_spec (self other : AddressRange) :
    AddressRange.non_overlapping_ranges self other ⦃ before after =>
      (∀ addr, (before.containsModel addr ∨ after.containsModel addr) ↔
        self.containsModel addr ∧ ¬other.containsModel addr) ∧
      (∀ addr, ¬(before.containsModel addr ∧ after.containsModel addr)) ⦄ := by
  step with non_overlapping_ranges_bounds_spec as ⟨before, after, hbounds⟩
  by_cases ho : other.isEmptyModel
  · simp only [ho, ↓reduceIte] at hbounds
    rcases hbounds with ⟨rfl, hafter⟩
    simp only [containsModel, isEmptyModel] at *
    constructor <;> intro addr <;> omega
  · simp only [ho, ↓reduceIte] at hbounds
    rcases hbounds with ⟨hbefore, hafter⟩
    simp only [containsModel, isEmptyModel] at *
    split_ifs at hbefore hafter
    all_goals constructor <;> intro addr <;> omega

@[step]
theorem len_spec (self : AddressRange) :
    AddressRange.len self ⦃ opt =>
      if self.lenModel ≤ U64.max then
        ∃ n, opt = some n ∧ n.val = self.lenModel
      else
        opt = none ⦄ := by
  unfold AddressRange.len
  step
  split
  · simp_all [lenModel]
  · step
    have h := U64.checked_add_bv_spec i 1#u64
    split at h <;> simp_all [lenModel, Nat.not_lt_of_ge]

/-- Splitting outside the range or at its start returns the original range and an empty range. -/
@[step]
theorem split_at_spec (self : AddressRange) (split_start : U64) :
    AddressRange.split_at self split_start ⦃ before after =>
      if split_start = self.start ∨ ¬self.containsModel split_start.val then
        before = self ∧ after.isEmptyModel
      else
        before.start = self.start ∧
        before.end.val = split_start.val - 1 ∧
        after.start = split_start ∧
        after.end = self.end ⦄ := by
  unfold AddressRange.split_at
  split
  · step
    simp_all [containsModel]
    scalar_tac
  · split
    · step
      simp_all [containsModel]
    · step
      simp_all [containsModel]
      omega

/-- Custom `PartialEq` for `AddressRange`: two ranges are equal iff both are empty,
    or both are non-empty with identical `start` and `end`. -/
@[step]
theorem eq_spec (self other : AddressRange) :
    AddressRange.Insts.CoreCmpPartialEqAddressRange.eq self other ⦃ b =>
      b = true ↔
        (self.isEmptyModel ∧ other.isEmptyModel) ∨
        (¬self.isEmptyModel ∧ ¬other.isEmptyModel ∧ self = other) ⦄ := by
  unfold AddressRange.Insts.CoreCmpPartialEqAddressRange.eq
  unfold AddressRange.Insts.CoreCmpOrd.cmp
  step
  step
  split
  · split <;> simp_all [core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
  · split
    · simp_all [core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
    · simp only [core.cmp.impls.OrdU64.cmp, lift,
        core.cmp.Ordering.then_with,
        address_range.OrdAddressRange.cmp.closure.Insts.CoreOpsFunctionFnOnceTupleOrdering.call_once,
        core.cmp.Ordering.Insts.CoreCmpPartialEqOrdering.eq]
      cases self; cases other
      simp_all [compare, compareOfLessAndEq]
      (split_ifs at * <;> simp_all); scalar_tac

/-- The order used by the free-region set, restricted to nonempty ranges. -/
abbrev ltModel (r s : AddressRange) : Prop :=
  r.start.val < s.start.val ∨ (r.start.val = s.start.val ∧ r.end.val < s.end.val)

@[step]
theorem cmp_nonempty_spec (r s : AddressRange)
    (hr : ¬r.isEmptyModel) (hs : ¬s.isEmptyModel) :
    Insts.CoreCmpOrd.cmp r s ⦃ o =>
      (o = .eq ↔ r = s) ∧ (o = .lt ↔ r.ltModel s) ∧ (o = .gt ↔ s.ltModel r) ⦄ := by
  unfold Insts.CoreCmpOrd.cmp
  simp [is_empty, isEmptyModel] at hr hs ⊢
  simp [core.cmp.Ordering.then_with,
    address_range.OrdAddressRange.cmp.closure.Insts.CoreOpsFunctionFnOnceTupleOrdering.call_once,
    compare, compareOfLessAndEq, ltModel]
  cases r; cases s
  simp_all
  split_ifs <;> simp_all [lift] <;> scalar_tac

end resources.address_range.AddressRange
