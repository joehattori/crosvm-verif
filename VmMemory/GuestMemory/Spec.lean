module
public import VmMemory.MemoryRegion.Spec
import all Aeneas.Std.Scalar.Ops.Add
import Utils.CoreSpec
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address

namespace vm_memory.guest_memory.GuestMemory

/-- The regions in slice order. -/
abbrev regionList (self : GuestMemory) : List MemoryRegion := self.regions.val.val

/-- Every region's exclusive end is representable, and each region ends at or
    before every later region starts. -/
def RegionsWellFormed (regions : List MemoryRegion) : Prop :=
  (∀ r ∈ regions, r.ValidBounds) ∧ regions.Pairwise MemoryRegion.EndsBefore

/-- Well-formed guest memory: its regions are well-formed. -/
def WellFormed (self : GuestMemory) : Prop :=
  RegionsWellFormed self.regionList

/-- Sum of the region lengths, as computed by `memory_size` without overflow. -/
def totalLength (self : GuestMemory) : Nat :=
  (self.regionList.map fun r => r.mapping.length.val).sum

theorem WellFormed.validBounds {self : GuestMemory} (h : self.WellFormed)
    {r : MemoryRegion} (hr : r ∈ self.regionList) : r.ValidBounds :=
  h.1 r hr

/-- Regions are sorted by guest base. -/
theorem WellFormed.sorted {self : GuestMemory} (h : self.WellFormed) :
    self.regionList.Pairwise (fun a b => a.guest_base.val ≤ b.guest_base.val) :=
  h.2.imp fun hab => by unfold MemoryRegion.EndsBefore at hab; omega

/-- At most one region contains a given address. -/
theorem WellFormed.index_eq_of_mem {self : GuestMemory} (h : self.WellFormed)
    {i j : Nat} (hi : i < self.regionList.length) (hj : j < self.regionList.length)
    {addr : Nat}
    (hci : self.regionList[i].guest_base.val ≤ addr ∧
      addr < self.regionList[i].guest_base.val + self.regionList[i].mapping.length.val)
    (hcj : self.regionList[j].guest_base.val ≤ addr ∧
      addr < self.regionList[j].guest_base.val + self.regionList[j].mapping.length.val) :
    i = j := by
  have hp := List.pairwise_iff_getElem.mp h.2
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := hp i j hi hj hij
    unfold MemoryRegion.EndsBefore at this
    omega
  · exact hij
  · have := hp j i hj hi hij
    unfold MemoryRegion.EndsBefore at this
    omega

private theorem start_add_sum_le (l : List MemoryRegion) (hl : l.Pairwise MemoryRegion.EndsBefore)
    (start bound : Nat) (hStart : ∀ r ∈ l, start ≤ r.guest_base.val)
    (hBound : ∀ r ∈ l, r.guest_base.val + r.mapping.length.val ≤ bound)
    (hle : start ≤ bound) :
    start + (l.map fun r => r.mapping.length.val).sum ≤ bound := by
  induction l generalizing start with
  | nil => simpa using hle
  | cons r rs ih =>
    rw [List.pairwise_cons] at hl
    have hr := hStart r (by simp)
    have hrBound := hBound r (by simp)
    have hrs := ih hl.2 (r.guest_base.val + r.mapping.length.val) (fun s hs => hl.1 s hs)
      (fun s hs => hBound s (by simp [hs])) hrBound
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The total length fits in `u64`, so summing region sizes cannot overflow. -/
theorem WellFormed.totalLength_le {self : GuestMemory} (h : self.WellFormed) :
    self.totalLength ≤ U64.max := by
  have := start_add_sum_le self.regionList h.2 0 U64.max (fun _ _ => Nat.zero_le _)
    (fun r hr => h.validBounds hr) (Nat.zero_le _)
  simpa [totalLength] using this

/-! ### Slice iterator `any` -/

/-- `any` over a slice iterator accepts exactly when some remaining element
    satisfies `P`, for a pure predicate that leaves its state unchanged. -/
theorem _root_.core.slice.iter.Iter.any_spec {T F : Type}
    (fnMutInst : core.ops.function.FnMut F T Bool) (P : T → Prop) (f : F)
    (hf : ∀ x, fnMutInst.call_mut f x ⦃ r => r.2 = f ∧ (r.1 = true ↔ P x) ⦄)
    (it : core.slice.iter.Iter T) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any fnMutInst it f
      ⦃ r => r.1 = true ↔ ∃ x ∈ it.slice.val.drop it.i, P x ⦄ := by
  suffices ∀ n (it : core.slice.iter.Iter T), it.slice.val.length - it.i = n →
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any fnMutInst it f
        ⦃ r => r.1 = true ↔ ∃ x ∈ it.slice.val.drop it.i, P x ⦄ from this _ it rfl
  intro n
  induction n with
  | zero =>
    intro it hn
    rw [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any]
    have : ¬ it.i < it.slice.val.length := by omega
    simp only [this, ↓reduceDIte, WP.spec_ok, Bool.false_eq_true, false_iff, not_exists, not_and]
    intro x hx
    simp [List.drop_eq_nil_of_le (by omega : it.slice.val.length ≤ it.i)] at hx
  | succ n ih =>
    intro it hn
    rw [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any]
    have hlt : it.i < it.slice.val.length := by omega
    have hdrop : it.slice.val.drop it.i = it.slice.val[it.i] :: it.slice.val.drop (it.i + 1) :=
      List.drop_eq_getElem_cons hlt
    simp only [hlt, ↓reduceDIte]
    apply WP.spec_bind (hf it.slice.val[it.i])
    rintro ⟨b, f'⟩ ⟨hf', hb⟩
    simp only at hf' hb
    subst hf'
    cases b with
    | true =>
      simp only [↓reduceIte, WP.spec_ok, true_iff, hdrop]
      exact ⟨_, List.mem_cons_self, hb.mp rfl⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply WP.spec_mono (ih { it with i := it.i + 1 } (by simp; omega))
      intro r hr
      have : ¬ P it.slice.val[it.i] := fun hp => by simpa using hb.mpr hp
      rw [hr, hdrop]
      simp only [List.mem_cons, exists_eq_or_imp, this, false_or]

/-! ### Slice iterator `find` -/

/-- `find` over a slice iterator returns the first remaining element that
    satisfies `P`, for a pure predicate that leaves its state unchanged. -/
theorem _root_.core.slice.iter.Iter.find_spec {T F : Type}
    (fnMutInst : core.ops.function.FnMut F T Bool) (P : T → Prop) [DecidablePred P] (f : F)
    (hf : ∀ x, fnMutInst.call_mut f x ⦃ r => r.2 = f ∧ (r.1 = true ↔ P x) ⦄)
    (it : core.slice.iter.Iter T) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find fnMutInst it f
      ⦃ r => r.1 = (it.slice.val.drop it.i).find? (fun x => decide (P x)) ⦄ := by
  suffices ∀ n (it : core.slice.iter.Iter T), it.slice.val.length - it.i = n →
      core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find fnMutInst it f
        ⦃ r => r.1 = (it.slice.val.drop it.i).find? (fun x => decide (P x)) ⦄ from this _ it rfl
  intro n
  induction n with
  | zero =>
    intro it hn
    rw [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find]
    have : ¬ it.i < it.slice.val.length := by omega
    simp [this, List.drop_eq_nil_of_le (by omega : it.slice.val.length ≤ it.i)]
  | succ n ih =>
    intro it hn
    rw [core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find]
    have hlt : it.i < it.slice.val.length := by omega
    have hdrop : it.slice.val.drop it.i = it.slice.val[it.i] :: it.slice.val.drop (it.i + 1) :=
      List.drop_eq_getElem_cons hlt
    simp only [hlt, ↓reduceDIte]
    apply WP.spec_bind (hf it.slice.val[it.i])
    rintro ⟨b, f'⟩ ⟨hf', hb⟩
    simp only at hf' hb
    subst hf'
    cases b with
    | true =>
      simp only [↓reduceIte, WP.spec_ok, hdrop]
      rw [List.find?_cons_of_pos (by simpa using hb.mp rfl)]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply WP.spec_mono (ih { it with i := it.i + 1 } (by simp; omega))
      intro r hr
      have : ¬ P it.slice.val[it.i] := fun hp => by simpa using hb.mpr hp
      rw [hr, hdrop, List.find?_cons_of_neg (by simpa using this)]

/-! ### Accessors -/

@[step]
theorem locked_spec (self : GuestMemory) :
    impl.locked self ⦃ b => b = self.locked ⦄ := by
  simp [impl.locked]

@[step]
theorem use_punchhole_locked_spec (self : GuestMemory) :
    impl.use_punchhole_locked self ⦃ b => b = self.use_punchhole_locked ⦄ := by
  simp [impl.use_punchhole_locked]

private theorem usize_cast_u64_val (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

@[step]
theorem num_regions_spec (self : GuestMemory) :
    self.num_regions ⦃ n => n.val = self.regionList.length ⦄ := by
  simp [num_regions]

/-! ### `address_in_range` -/

/-- Some region's `contains` accepts the address. -/
def AddressInRangeOutcome (self : GuestMemory) (addr : GuestAddress) (b : Bool) : Prop :=
  b = true ↔ ∃ r ∈ self.regionList, r.ContainsOutcome addr true

@[step]
theorem address_in_range_spec (self : GuestMemory) (addr : GuestAddress) :
    self.address_in_range addr ⦃ b => self.AddressInRangeOutcome addr b ⦄ := by
  unfold address_in_range
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  have hf : ∀ r,
      address_in_range.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
        addr r ⦃ p => p.2 = addr ∧ (p.1 = true ↔ r.ContainsOutcome addr true) ⦄ := by
    intro r
    unfold address_in_range.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
    apply WP.spec_bind (MemoryRegion.contains_spec r addr)
    intro b hb
    simpa using hb.eq_true_iff
  apply WP.spec_bind (core.slice.iter.Iter.any_spec _ _ addr hf _)
  rintro ⟨b, _⟩ hb
  simpa [AddressInRangeOutcome] using hb

/-- For well-formed memory, an address is in range exactly when it lies in the
    mathematical half-open interval of some region. -/
theorem WellFormed.addressInRange_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {b : Bool} (hOut : self.AddressInRangeOutcome addr b) :
    b = true ↔ ∃ r ∈ self.regionList,
      r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val := by
  rw [show (b = true ↔ _) from hOut]
  apply exists_congr
  intro r
  constructor
  · rintro ⟨hr, endAddr, he, hc⟩
    have hin := hc.mp rfl
    rw [he.val_eq_of_valid (h.validBounds hr)] at hin
    exact ⟨hr, hin⟩
  · rintro ⟨hr, hc⟩
    obtain ⟨endAddr, he⟩ := MemoryRegion.EndOutcome.exists r
    refine ⟨hr, endAddr, he, iff_of_true rfl ?_⟩
    rw [he.val_eq_of_valid (h.validBounds hr)]
    exact hc

/-! ### `range_overlap` -/

/-- Some region starts before `end` and its endpoint, as computed by
    `MemoryRegion::end`, lies after `start`. -/
def RangeOverlapOutcome (self : GuestMemory) (start «end» : GuestAddress) (b : Bool) : Prop :=
  b = true ↔ ∃ r ∈ self.regionList, r.guest_base.val < «end».val ∧
    ∃ regionEnd, r.EndOutcome regionEnd ∧ start.val < regionEnd.val

@[step]
theorem range_overlap_spec (self : GuestMemory) (start «end» : GuestAddress) :
    self.range_overlap start «end» ⦃ b => self.RangeOverlapOutcome start «end» b ⦄ := by
  unfold range_overlap
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  have hf : ∀ r,
      range_overlap.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
        («end», start) r ⦃ p => p.2 = («end», start) ∧
          (p.1 = true ↔ r.guest_base.val < «end».val ∧
            ∃ regionEnd, r.EndOutcome regionEnd ∧ start.val < regionEnd.val) ⦄ := by
    intro r
    unfold range_overlap.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
    step as ⟨s, hs⟩
    step as ⟨b, hb⟩
    subst hs
    split
    · step as ⟨regionEnd, he⟩
      step as ⟨b1, hb1⟩
      refine ⟨rfl, ?_⟩
      rw [hb1]
      constructor
      · intro hlt
        exact ⟨hb.mp (by assumption), regionEnd, he, hlt⟩
      · rintro ⟨_, regionEnd', he', hlt⟩
        rwa [he'.trans he.symm] at hlt
    · simp_all
      rfl
  apply WP.spec_bind (core.slice.iter.Iter.any_spec _ _ («end», start) hf _)
  rintro ⟨b, _⟩ hb
  simpa [RangeOverlapOutcome] using hb

/-- For well-formed memory, `range_overlap` holds exactly when `[start, end)`
    intersects the mathematical half-open interval of some region. -/
theorem WellFormed.rangeOverlap_iff {self : GuestMemory} (h : self.WellFormed)
    {start «end» : GuestAddress} {b : Bool} (hOut : self.RangeOverlapOutcome start «end» b) :
    b = true ↔ ∃ r ∈ self.regionList, r.guest_base.val < «end».val ∧
      start.val < r.guest_base.val + r.mapping.length.val := by
  rw [show (b = true ↔ _) from hOut]
  apply exists_congr
  intro r
  constructor
  · rintro ⟨hr, hlt, regionEnd, he, hs⟩
    exact ⟨hr, hlt, by rwa [he.val_eq_of_valid (h.validBounds hr)] at hs⟩
  · rintro ⟨hr, hlt, hs⟩
    obtain ⟨regionEnd, he⟩ := MemoryRegion.EndOutcome.exists r
    exact ⟨hr, hlt, regionEnd, he, by rwa [he.val_eq_of_valid (h.validBounds hr)]⟩

/-! ### `is_valid_range` -/

/-- Empty requests are rejected. Otherwise the last byte `start + (length - 1)`
    is computed with `checked_add`: overflow is rejected, and an in-range last
    byte is accepted exactly when some region starts at or before `start` and
    its endpoint, as computed by `MemoryRegion::end`, lies after the last byte. -/
def IsValidRangeOutcome (self : GuestMemory) (start : GuestAddress) (length : U64)
    (b : Bool) : Prop :=
  if length = 0#u64 then b = false
  else ∃ last : U64, last.val = length.val - 1 ∧
    match U64.checked_add start last with
    | none => b = false
    | some lastAddr => b = true ↔ ∃ r ∈ self.regionList, r.guest_base.val ≤ start.val ∧
      ∃ regionEnd, r.EndOutcome regionEnd ∧ lastAddr.val < regionEnd.val

@[step]
theorem is_valid_range_spec (self : GuestMemory) (start : GuestAddress) (length : U64) :
    self.is_valid_range start length ⦃ b => self.IsValidRangeOutcome start length b ⦄ := by
  unfold is_valid_range
  by_cases h0 : length = 0#u64
  · simp [h0, IsValidRangeOutcome]
  · simp only [h0, ↓reduceIte, IsValidRangeOutcome]
    step as ⟨last, hlast⟩
    step as ⟨o, ho⟩
    subst ho
    refine WP.spec_mono (P₀ := fun b => match U64.checked_add start last with
      | none => b = false
      | some lastAddr => b = true ↔ ∃ r ∈ self.regionList, r.guest_base.val ≤ start.val ∧
        ∃ regionEnd, r.EndOutcome regionEnd ∧ lastAddr.val < regionEnd.val) ?_
      (fun b hb => ⟨last, hlast, hb⟩)
    cases U64.checked_add start last with
    | none => simp
    | some lastAddr =>
      have hf : ∀ r,
          is_valid_range.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
            (start, lastAddr) r ⦃ p => p.2 = (start, lastAddr) ∧
              (p.1 = true ↔ r.guest_base.val ≤ start.val ∧
                ∃ regionEnd, r.EndOutcome regionEnd ∧ lastAddr.val < regionEnd.val) ⦄ := by
        intro r
        unfold is_valid_range.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionBool.call_mut
        step as ⟨s, hs⟩
        step as ⟨b, hb⟩
        subst hs
        split
        · step as ⟨regionEnd, he⟩
          step as ⟨b1, hb1⟩
          refine ⟨rfl, ?_⟩
          rw [hb1]
          constructor
          · intro hlt
            exact ⟨hb.mp (by assumption), regionEnd, he, hlt⟩
          · rintro ⟨_, regionEnd', he', hlt⟩
            rwa [he'.trans he.symm] at hlt
        · simp_all
          rfl
      simp only [core.slice.Slice.iter, bind_ok]
      apply WP.spec_bind (core.slice.iter.Iter.any_spec _ _ (start, lastAddr) hf _)
      rintro ⟨b, _⟩ hb
      simpa using hb

/-- For well-formed memory, `is_valid_range` holds exactly when the request is
    non-empty and `[start, start + length)` lies within a single region. -/
theorem WellFormed.isValidRange_iff {self : GuestMemory} (h : self.WellFormed)
    {start : GuestAddress} {length : U64} {b : Bool}
    (hOut : self.IsValidRangeOutcome start length b) :
    b = true ↔ 0 < length.val ∧ ∃ r ∈ self.regionList, r.guest_base.val ≤ start.val ∧
      start.val + length.val ≤ r.guest_base.val + r.mapping.length.val := by
  unfold IsValidRangeOutcome at hOut
  split at hOut
  · rename_i h0
    subst hOut
    simp [h0]
  · rename_i h0
    have hpos : 0 < length.val := by
      have : length.val ≠ 0 := fun hz => h0 (by scalar_tac)
      omega
    obtain ⟨last, hlast, hm⟩ := hOut
    have hAdd := U64.checked_add_bv_spec start last
    cases ho : U64.checked_add start last with
    | none =>
      simp only [ho] at hm hAdd
      subst hm
      simp only [Bool.false_eq_true, false_iff, not_and, not_exists]
      intro _ r hr hle hfit
      have := h.validBounds hr
      unfold MemoryRegion.ValidBounds at this
      omega
    | some lastAddr =>
      simp only [ho] at hm hAdd
      rw [hm]
      constructor
      · rintro ⟨r, hr, hle, regionEnd, he, hlt⟩
        rw [he.val_eq_of_valid (h.validBounds hr)] at hlt
        exact ⟨hpos, r, hr, hle, by omega⟩
      · rintro ⟨-, r, hr, hle, hfit⟩
        obtain ⟨regionEnd, he⟩ := MemoryRegion.EndOutcome.exists r
        exact ⟨r, hr, hle, regionEnd, he, by rw [he.val_eq_of_valid (h.validBounds hr)]; omega⟩

/-! ### `checked_offset` -/

/-- Overflow of `addr + offset` yields `None`; otherwise the sum is returned
    exactly when `address_in_range` accepts it. -/
def CheckedOffsetOutcome (self : GuestMemory) (addr : GuestAddress) (offset : U64)
    (result : Option GuestAddress) : Prop :=
  match U64.checked_add addr offset with
  | none => result = none
  | some target =>
    ∃ inRange, self.AddressInRangeOutcome target inRange ∧
      result = if inRange then some target else none

@[step]
theorem checked_offset_spec (self : GuestMemory) (addr : GuestAddress) (offset : U64) :
    self.checked_offset addr offset ⦃ r => self.CheckedOffsetOutcome addr offset r ⦄ := by
  unfold checked_offset
  step as ⟨o, ho⟩
  simp only [CheckedOffsetOutcome, ← ho]
  cases o with
  | none => simp [core.option.Option.and_then]
  | some target =>
    simp only [core.option.Option.and_then,
      checked_offset.closure.Insts.CoreOpsFunctionFnOnceTupleGuestAddressOptionGuestAddress.call_once]
    step as ⟨inRange, hin⟩
    cases inRange <;>
      simp only [↓reduceIte, Bool.false_eq_true, WP.spec_ok] <;> exact ⟨_, hin, rfl⟩

/-- For well-formed memory, `checked_offset` returns `some target` exactly when
    `target = addr + offset` lies in the mathematical half-open interval of some
    region. -/
theorem WellFormed.checkedOffset_eq_some_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {offset : U64} {result : Option GuestAddress}
    (hOut : self.CheckedOffsetOutcome addr offset result) (target : GuestAddress) :
    result = some target ↔ target.val = addr.val + offset.val ∧
      ∃ r ∈ self.regionList, r.guest_base.val ≤ target.val ∧
        target.val < r.guest_base.val + r.mapping.length.val := by
  have hAdd := U64.checked_add_bv_spec addr offset
  unfold CheckedOffsetOutcome at hOut
  cases ho : U64.checked_add addr offset with
  | none =>
    simp only [ho] at hOut hAdd
    subst hOut
    simp only [reduceCtorEq, false_iff, not_and, not_exists]
    intro hsum r hr _ hlt
    have := h.validBounds hr
    unfold MemoryRegion.ValidBounds at this
    omega
  | some sum =>
    simp only [ho] at hOut hAdd
    obtain ⟨inRange, hin, hr⟩ := hOut
    have hiff := h.addressInRange_iff hin
    subst hr
    cases inRange with
    | true =>
      simp only [↓reduceIte, Option.some.injEq]
      constructor
      · rintro rfl
        exact ⟨hAdd.2.1, hiff.mp rfl⟩
      · rintro ⟨hval, -⟩
        exact UScalar.eq_of_val_eq (by rw [hval, hAdd.2.1])
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, reduceCtorEq, false_iff, not_and]
      intro hval hex
      have heq : target = sum := UScalar.eq_of_val_eq (by rw [hval, hAdd.2.1])
      subst heq
      exact absurd (hiff.mpr hex) (by simp)

/-! ### `memory_size` -/

/-- Checked summation over a slice iterator mapped through a pure closure
    returns `acc` plus the sum of the remaining mapped values, provided that
    total fits in `u64`. -/
theorem _root_.U64.Insts.CoreIterTraitsAccumSumU64.sumFrom_map_slice_spec {T F : Type}
    (fInst : core.ops.function.FnMut F T U64) (f : F) (g : T → U64)
    (hf : ∀ x, fInst.call_mut f x = ok (g x, f)) (s : Slice T) :
    ∀ (i : Nat) (acc : U64),
      acc.val + ((s.val.drop i).map fun x => (g x).val).sum ≤ U64.max →
      U64.Insts.CoreIterTraitsAccumSumU64.sumFrom
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter T) fInst) acc ⟨⟨s, i⟩, f⟩
        ⦃ r => r.val = acc.val + ((s.val.drop i).map fun x => (g x).val).sum ⦄ := by
  suffices ∀ n (i : Nat) (acc : U64), s.val.length - i = n →
      acc.val + ((s.val.drop i).map fun x => (g x).val).sum ≤ U64.max →
      U64.Insts.CoreIterTraitsAccumSumU64.sumFrom
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter T) fInst) acc ⟨⟨s, i⟩, f⟩
        ⦃ r => r.val = acc.val + ((s.val.drop i).map fun x => (g x).val).sum ⦄ from
    fun i acc => this _ i acc rfl
  intro n
  induction n with
  | zero =>
    intro i acc hn _
    have hge : s.val.length ≤ i := by omega
    rw [U64.Insts.CoreIterTraitsAccumSumU64.sumFrom.eq_def]
    simp [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      core.slice.iter.IteratorSliceIter.next, Nat.not_lt.mpr hge,
      List.drop_eq_nil_of_le hge]
  | succ n ih =>
    intro i acc hn hfit
    have hlt : i < s.val.length := by omega
    have hdrop : s.val.drop i = s.val[i] :: s.val.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [hdrop, List.map_cons, List.sum_cons] at hfit ⊢
    rw [U64.Insts.CoreIterTraitsAccumSumU64.sumFrom.eq_def]
    simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      core.slice.iter.IteratorSliceIter.next, Slice.len_val, hlt, ↓reduceDIte, bind_ok, hf]
    step as ⟨acc', hacc'⟩
    change acc'.val = acc.val + (g s.val[i]).val at hacc'
    apply WP.spec_mono (ih (i + 1) acc' (by omega) (by omega))
    intro r hr
    omega

private theorem u64_add_overflow (x y : U64) (h : U64.max < x.val + y.val) :
    x + y = fail .integerOverflow := by
  have hlt : ¬ (x.val + y.val < 18446744073709551616) := by scalar_tac
  simp [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, Result.ofOption]
  simp only [Add.add, Nat.add_eq] at *
  simp [hlt]

private theorem u64_add_ok (x y : U64) (h : x.val + y.val ≤ U64.max) :
    ∃ z : U64, x + y = ok z ∧ z.val = x.val + y.val := by
  have hlt : x.val + y.val < 18446744073709551616 := by scalar_tac
  simp [HAdd.hAdd, UScalar.add, UScalar.tryMk, UScalar.tryMkOpt, Result.ofOption]
  simp only [Add.add, Nat.add_eq] at *
  simp [hlt]

private theorem sliceIter_next_of_lt {T : Type} (s : Slice T) (i : Nat)
    (h : i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (some s.val[i], ⟨s, i + 1⟩) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]
  rfl

/-- If `acc` plus the remaining mapped values exceeds `u64::MAX`, checked
    summation fails with an integer overflow (a panic in Rust). -/
theorem _root_.U64.Insts.CoreIterTraitsAccumSumU64.sumFrom_map_slice_overflow {T F : Type}
    (fInst : core.ops.function.FnMut F T U64) (f : F) (g : T → U64)
    (hf : ∀ x, fInst.call_mut f x = ok (g x, f)) (s : Slice T) :
    ∀ (i : Nat) (acc : U64),
      U64.max < acc.val + ((s.val.drop i).map fun x => (g x).val).sum →
      U64.Insts.CoreIterTraitsAccumSumU64.sumFrom
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter T) fInst) acc ⟨⟨s, i⟩, f⟩ =
        fail .integerOverflow := by
  suffices ∀ n (i : Nat) (acc : U64), s.val.length - i = n →
      U64.max < acc.val + ((s.val.drop i).map fun x => (g x).val).sum →
      U64.Insts.CoreIterTraitsAccumSumU64.sumFrom
          (core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
            (core.iter.traits.iterator.IteratorSliceIter T) fInst) acc ⟨⟨s, i⟩, f⟩ =
        fail .integerOverflow from
    fun i acc => this _ i acc rfl
  intro n
  induction n with
  | zero =>
    intro i acc hn hover
    have hge : s.val.length ≤ i := by omega
    simp [List.drop_eq_nil_of_le hge] at hover
    scalar_tac
  | succ n ih =>
    intro i acc hn hover
    have hlt : i < s.val.length := by omega
    have hdrop : s.val.drop i = s.val[i] :: s.val.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [hdrop, List.map_cons, List.sum_cons] at hover
    rw [U64.Insts.CoreIterTraitsAccumSumU64.sumFrom.eq_def]
    simp only [core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
      sliceIter_next_of_lt s i hlt]
    simp [hf]
    by_cases hstep : acc.val + (g s.val[i]).val ≤ U64.max
    · obtain ⟨acc', hacc', hval⟩ := u64_add_ok acc (g s.val[i]) hstep
      rw [hacc', bind_ok]
      exact ih (i + 1) acc' (by omega) (by omega)
    · rw [u64_add_overflow _ _ (by omega)]
      simp

private theorem usize_cast_u64_val' (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

/-- `memory_size` returns the total region length whenever it fits in `u64`.
    Each region contributes `mapping.size() as u64`, which is exact. -/
@[step]
theorem memory_size_spec (self : GuestMemory) (h : self.totalLength ≤ U64.max) :
    self.memory_size ⦃ size => size.val = self.totalLength ⦄ := by
  unfold memory_size
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok,
    core.iter.traits.iterator.Iterator.map.default, core.iter.traits.iterator.Iterator.sum.default,
    U64.Insts.CoreIterTraitsAccumSumU64.sum]
  have hf : ∀ r : MemoryRegion,
      memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64.call_mut () r =
        ok (UScalar.cast .U64 r.mapping.length, ()) := by
    intro r
    simp [memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64.call_mut,
      base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, lift]
  have hmap : (fun r : MemoryRegion => (UScalar.cast .U64 r.mapping.length).val) =
      fun r => r.mapping.length.val := by
    funext r
    exact usize_cast_u64_val' _
  have := U64.Insts.CoreIterTraitsAccumSumU64.sumFrom_map_slice_spec
    memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64 ()
    (fun r => UScalar.cast .U64 r.mapping.length) hf self.regions.val
    0 0#u64 (by simpa [hmap, totalLength] using h)
  simpa [hmap, totalLength] using this

/-- If the total exceeds `u64::MAX`, `memory_size` panics on overflow;
    `WellFormed.totalLength_le` rules this out. -/
theorem memory_size_overflow (self : GuestMemory) (h : U64.max < self.totalLength) :
    self.memory_size = fail .integerOverflow := by
  unfold memory_size
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok,
    core.iter.traits.iterator.Iterator.map.default, core.iter.traits.iterator.Iterator.sum.default,
    U64.Insts.CoreIterTraitsAccumSumU64.sum]
  have hf : ∀ r : MemoryRegion,
      memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64.call_mut () r =
        ok (UScalar.cast .U64 r.mapping.length, ()) := by
    intro r
    simp [memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64.call_mut,
      base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, lift]
  have hmap : (fun r : MemoryRegion => (UScalar.cast .U64 r.mapping.length).val) =
      fun r => r.mapping.length.val := by
    funext r
    exact usize_cast_u64_val' _
  exact U64.Insts.CoreIterTraitsAccumSumU64.sumFrom_map_slice_overflow
    memory_size.closure.Insts.CoreOpsFunctionFnMutTupleShared0MemoryRegionU64 ()
    (fun r => UScalar.cast .U64 r.mapping.length) hf self.regions.val
    0 0#u64 (by simpa [hmap, totalLength] using h)

unseal Result in
/-- A successful total-correctness spec pins down the result. -/
private theorem spec_eq_ok {α : Type _} {m : Result α} {p : α → Prop} (h : m ⦃ x => p x ⦄) :
    ∃ x, m = ok x ∧ p x := by
  unfold WP.spec at h
  exact h.induction (P := fun t _ => ∃ x, t = .ret x ∧ p x) (fun v _ hv => ⟨v, rfl, hv⟩)
    (fun e _ _ hwp => by cases e; exact hwp.elim)

/-! ### Region lookup -/

open Classical in
/-- The first region whose `contains` accepts the address. `find_region` and
    `offset_from_base` look it up with `Iter::find`. -/
noncomputable def containingRegion (self : GuestMemory) (addr : GuestAddress) :
    Option MemoryRegion :=
  self.regionList.find? (fun r => decide (r.ContainsOutcome addr true))

theorem containingRegion_eq_some {self : GuestMemory} {addr : GuestAddress} {r : MemoryRegion}
    (h : self.containingRegion addr = some r) :
    r ∈ self.regionList ∧ r.ContainsOutcome addr true := by
  classical
  unfold containingRegion at h
  have hp := List.find?_some h
  simp only [decide_eq_true_eq] at hp
  exact ⟨List.mem_of_find?_eq_some h, hp⟩

/-- `Iter::find` with a closure whose result is `contains` returns the
    containing region. -/
private theorem find_containing_spec {F : Type} (self : GuestMemory) (addr : GuestAddress)
    (fnMutInst : core.ops.function.FnMut F MemoryRegion Bool) (f : F)
    (hf : ∀ r, fnMutInst.call_mut f r ⦃ p => p.2 = f ∧ (p.1 = true ↔ r.ContainsOutcome addr true) ⦄) :
    core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find fnMutInst
        ⟨self.regions.val, 0⟩ f
      ⦃ r => r.1 = self.containingRegion addr ⦄ := by
  classical
  apply WP.spec_mono (core.slice.iter.Iter.find_spec fnMutInst _ f hf _)
  intro r hr
  rw [hr]
  rfl

/-- A closure that calls `contains` on its region argument. -/
private theorem contains_closure_spec (addr : GuestAddress) (r : MemoryRegion) :
    (do let b ← r.contains addr; ok (b, addr)) ⦃ p =>
      p.2 = addr ∧ (p.1 = true ↔ r.ContainsOutcome addr true) ⦄ := by
  apply WP.spec_bind (MemoryRegion.contains_spec r addr)
  intro b hb
  simpa using hb.eq_true_iff

/-- For a region with representable end, `contains` accepts exactly the
    addresses in its mathematical half-open interval. -/
private theorem containsOutcome_true_iff {r : MemoryRegion} (hv : r.ValidBounds)
    (addr : GuestAddress) :
    r.ContainsOutcome addr true ↔
      r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val := by
  constructor
  · rintro ⟨endAddr, he, hc⟩
    rw [← he.val_eq_of_valid hv]
    exact hc.mp rfl
  · intro hin
    obtain ⟨endAddr, he⟩ := MemoryRegion.EndOutcome.exists r
    exact ⟨endAddr, he, iff_of_true rfl (by rw [he.val_eq_of_valid hv]; exact hin)⟩

/-- For well-formed memory, the containing region is the region whose
    mathematical half-open interval contains the address. -/
theorem WellFormed.containingRegion_eq_some_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {r : MemoryRegion} :
    self.containingRegion addr = some r ↔ r ∈ self.regionList ∧
      r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val := by
  constructor
  · intro hc
    obtain ⟨hr, hcont⟩ := containingRegion_eq_some hc
    exact ⟨hr, (containsOutcome_true_iff (h.validBounds hr) addr).mp hcont⟩
  · rintro ⟨hr, hin⟩
    cases hc : self.containingRegion addr with
    | none =>
      classical
      unfold containingRegion at hc
      have := List.find?_eq_none.mp hc r hr
      simp only [decide_eq_true_eq] at this
      exact absurd ((containsOutcome_true_iff (h.validBounds hr) addr).mpr hin) this
    | some r' =>
      obtain ⟨hr', hcont'⟩ := containingRegion_eq_some hc
      have hin' := (containsOutcome_true_iff (h.validBounds hr') addr).mp hcont'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
      obtain rfl := h.index_eq_of_mem hj hi hin' hin
      rfl

/-- For well-formed memory, there is no containing region exactly when no
    region's mathematical half-open interval contains the address. -/
theorem WellFormed.containingRegion_eq_none_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} :
    self.containingRegion addr = none ↔ ∀ r ∈ self.regionList,
      ¬ (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) := by
  classical
  unfold containingRegion
  rw [List.find?_eq_none]
  apply forall₂_congr
  intro r hr
  simp only [decide_eq_true_eq]
  rw [containsOutcome_true_iff (h.validBounds hr) addr]

/-! ### `find_region` -/

/-- The containing region yields its mapping, the address's offset from the
    region start cast to `usize`, and its object offset. Without one, the error
    carries the address. -/
def FindRegionOutcome (self : GuestMemory) (addr : GuestAddress)
    (result : core.result.Result (base.mmap.MemoryMapping × Usize × U64)
      vm_memory.guest_memory.Error) : Prop :=
  match self.containingRegion addr with
  | none => result = .Err (.InvalidGuestAddress addr)
  | some r => ∃ offset, GuestAddress.OffsetFromOutcome addr r.guest_base offset ∧
      result = .Ok (r.mapping, UScalar.cast .Usize offset, r.obj_offset)

@[step]
theorem find_region_spec (self : GuestMemory) (addr : GuestAddress) :
    self.find_region addr ⦃ r => self.FindRegionOutcome addr r ⦄ := by
  unfold find_region
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  apply WP.spec_bind (find_containing_spec self addr _ addr fun r => contains_closure_spec addr r)
  rintro ⟨o, _⟩ ho
  change o = _ at ho
  subst ho
  unfold FindRegionOutcome
  cases hc : self.containingRegion addr with
  | none => simp [core.option.Option.ok_or, core.result.Result.map]
  | some r =>
    obtain ⟨-, endAddr, -, hcont⟩ := containingRegion_eq_some hc
    have hle : r.guest_base.val ≤ addr.val := (hcont.mp rfl).1
    simp only [core.option.Option.ok_or, core.result.Result.map,
      find_region.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0MemoryRegionTupleShared1MemoryMappingUsizeU64.call_once]
    step as ⟨start, hstart⟩
    subst hstart
    step as ⟨offset, hoffset⟩
    simp only [lift, bind_ok, WP.spec_ok]
    exact ⟨offset, hoffset, rfl⟩

/-- For well-formed memory, `find_region` succeeds exactly when some region's
    mathematical half-open interval contains the address, and then returns that
    region's mapping, the offset of the address within it, and its object
    offset. -/
theorem WellFormed.findRegion_eq_ok_iff [Platform64] {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {result} (hOut : self.FindRegionOutcome addr result)
    (mapping : base.mmap.MemoryMapping) (offset : Usize) (objOffset : U64) :
    result = .Ok (mapping, offset, objOffset) ↔ ∃ r ∈ self.regionList,
      (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) ∧
      mapping = r.mapping ∧ offset.val = addr.val - r.guest_base.val ∧
      objOffset = r.obj_offset := by
  unfold FindRegionOutcome at hOut
  cases hc : self.containingRegion addr with
  | none =>
    rw [hc] at hOut
    subst hOut
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro r hr hin
    exact absurd hin (h.containingRegion_eq_none_iff.mp hc r hr)
  | some r =>
    rw [hc] at hOut
    obtain ⟨o, ho, hres⟩ := hOut
    subst hres
    obtain ⟨hr, hin⟩ := h.containingRegion_eq_some_iff.mp hc
    unfold GuestAddress.OffsetFromOutcome at ho
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨r, hr, hin, rfl, by rw [Platform64.u64_cast_usize_val, ho], rfl⟩
    · rintro ⟨r', hr', hin', rfl, hoff, rfl⟩
      obtain rfl : r = r' :=
        Option.some.inj (hc.symm.trans (h.containingRegion_eq_some_iff.mpr ⟨hr', hin'⟩))
      exact ⟨rfl, UScalar.eq_of_val_eq (by rw [Platform64.u64_cast_usize_val, ho, hoff]), rfl⟩

/-- `find_region` fails only with `InvalidGuestAddress` for the given address,
    and for well-formed memory exactly when no region's mathematical half-open
    interval contains it. -/
theorem WellFormed.findRegion_eq_err_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {result} (hOut : self.FindRegionOutcome addr result)
    (e : vm_memory.guest_memory.Error) :
    result = .Err e ↔ e = .InvalidGuestAddress addr ∧ ∀ r ∈ self.regionList,
      ¬ (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) := by
  unfold FindRegionOutcome at hOut
  cases hc : self.containingRegion addr with
  | none =>
    rw [hc] at hOut
    subst hOut
    simp only [core.result.Result.Err.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, h.containingRegion_eq_none_iff.mp hc⟩
    · rintro ⟨rfl, -⟩
      rfl
  | some r =>
    rw [hc] at hOut
    obtain ⟨o, -, hres⟩ := hOut
    subst hres
    obtain ⟨hr, hin⟩ := h.containingRegion_eq_some_iff.mp hc
    simp only [reduceCtorEq, false_iff]
    rintro ⟨-, hall⟩
    exact hall r hr hin

/-! ### `offset_from_base` -/

/-- The unchecked sum in `offset_from_base` fits in `u64`: the containing
    region's object offset plus the address's offset into the region. -/
def OffsetFromBaseFits (self : GuestMemory) (addr : GuestAddress) : Prop :=
  match self.containingRegion addr with
  | none => True
  | some r => r.obj_offset.val + (addr.val - r.guest_base.val) ≤ U64.max

/-- The containing region yields its backing object and the address's offset
    into that object: the region's object offset plus the offset from the
    region start. Without one, the error carries the address. -/
def OffsetFromBaseOutcome (self : GuestMemory) (addr : GuestAddress)
    (result : core.result.Result
      (Dyn.{0, _} (fun _dyn => base.descriptor.AsRawDescriptor _dyn) × U64)
      vm_memory.guest_memory.Error) : Prop :=
  match self.containingRegion addr with
  | none => result = .Err (.InvalidGuestAddress addr)
  | some r => ∃ delta, GuestAddress.OffsetFromOutcome addr r.guest_base delta ∧
      ∃ offset : U64, offset.val = r.obj_offset.val + delta.val ∧
        result = .Ok (r.shared_obj.descriptor, offset)

@[step]
theorem offset_from_base_spec (self : GuestMemory) (addr : GuestAddress)
    (h : self.OffsetFromBaseFits addr) :
    self.offset_from_base addr ⦃ r => self.OffsetFromBaseOutcome addr r ⦄ := by
  unfold offset_from_base
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  apply WP.spec_bind (find_containing_spec self addr _ addr fun r => contains_closure_spec addr r)
  rintro ⟨o, _⟩ ho
  change o = _ at ho
  subst ho
  unfold OffsetFromBaseOutcome
  unfold OffsetFromBaseFits at h
  cases hc : self.containingRegion addr with
  | none => simp [core.option.Option.ok_or, core.result.Result.map]
  | some r =>
    rw [hc] at h
    obtain ⟨-, endAddr, -, hcont⟩ := containingRegion_eq_some hc
    have hle : r.guest_base.val ≤ addr.val := (hcont.mp rfl).1
    simp only [core.option.Option.ok_or, core.result.Result.map,
      offset_from_base.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0MemoryRegionPairShared1PU64.call_once]
    step as ⟨d, hd⟩
    step as ⟨start, hstart⟩
    subst hstart
    step as ⟨delta, hdelta⟩
    have hdv : delta.val = addr.val - r.guest_base.val := hdelta
    step as ⟨offset, hoffset⟩
    exact ⟨delta, hdelta, offset, hoffset, by rw [hd]⟩

/-- For well-formed memory, `offset_from_base` succeeds exactly when some
    region's mathematical half-open interval contains the address, and then
    returns that region's backing object and the address's offset into it. -/
theorem WellFormed.offsetFromBase_eq_ok_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {result} (hOut : self.OffsetFromBaseOutcome addr result)
    (descriptor : Dyn.{0, _} (fun _dyn => base.descriptor.AsRawDescriptor _dyn))
    (offset : U64) :
    result = .Ok (descriptor, offset) ↔ ∃ r ∈ self.regionList,
      (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) ∧
      descriptor = r.shared_obj.descriptor ∧
      offset.val = r.obj_offset.val + (addr.val - r.guest_base.val) := by
  unfold OffsetFromBaseOutcome at hOut
  cases hc : self.containingRegion addr with
  | none =>
    rw [hc] at hOut
    subst hOut
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro r hr hin
    exact absurd hin (h.containingRegion_eq_none_iff.mp hc r hr)
  | some r =>
    rw [hc] at hOut
    obtain ⟨delta, hdelta, o, ho, hres⟩ := hOut
    subst hres
    obtain ⟨hr, hin⟩ := h.containingRegion_eq_some_iff.mp hc
    unfold GuestAddress.OffsetFromOutcome at hdelta
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl⟩
      exact ⟨r, hr, hin, rfl, by rw [ho, hdelta]⟩
    · rintro ⟨r', hr', hin', rfl, hoff⟩
      obtain rfl : r = r' :=
        Option.some.inj (hc.symm.trans (h.containingRegion_eq_some_iff.mpr ⟨hr', hin'⟩))
      exact ⟨rfl, UScalar.eq_of_val_eq (by rw [ho, hoff, hdelta])⟩

/-- `offset_from_base` fails only with `InvalidGuestAddress` for the given
    address, and for well-formed memory exactly when no region's mathematical
    half-open interval contains it. -/
theorem WellFormed.offsetFromBase_eq_err_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {result} (hOut : self.OffsetFromBaseOutcome addr result)
    (e : vm_memory.guest_memory.Error) :
    result = .Err e ↔ e = .InvalidGuestAddress addr ∧ ∀ r ∈ self.regionList,
      ¬ (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) := by
  unfold OffsetFromBaseOutcome at hOut
  cases hc : self.containingRegion addr with
  | none =>
    rw [hc] at hOut
    subst hOut
    simp only [core.result.Result.Err.injEq]
    constructor
    · rintro rfl
      exact ⟨rfl, h.containingRegion_eq_none_iff.mp hc⟩
    · rintro ⟨rfl, -⟩
      rfl
  | some r =>
    rw [hc] at hOut
    obtain ⟨_, _, _, _, hres⟩ := hOut
    subst hres
    obtain ⟨hr, hin⟩ := h.containingRegion_eq_some_iff.mp hc
    simp only [reduceCtorEq, false_iff]
    rintro ⟨-, hall⟩
    exact hall r hr hin

/-- If the sum overflows, `offset_from_base` panics. -/
theorem offset_from_base_overflow (self : GuestMemory) (addr : GuestAddress)
    (h : ¬ self.OffsetFromBaseFits addr) :
    self.offset_from_base addr = fail .integerOverflow := by
  unfold OffsetFromBaseFits at h
  cases hc : self.containingRegion addr with
  | none => simp [hc] at h
  | some r =>
    rw [hc] at h
    obtain ⟨-, endAddr, -, hcont⟩ := containingRegion_eq_some hc
    have hle : r.guest_base.val ≤ addr.val := (hcont.mp rfl).1
    unfold offset_from_base
    simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
    obtain ⟨⟨o, it⟩, hfind, ho⟩ :=
      spec_eq_ok (find_containing_spec self addr
        offset_from_base.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared0MemoryRegionBool addr fun r => contains_closure_spec addr r)
    change o = _ at ho
    obtain ⟨d, hd, -⟩ := spec_eq_ok (BackingObject.as_ref_spec r.shared_obj)
    obtain ⟨delta, hdelta, hdv⟩ := spec_eq_ok (GuestAddress.offset_from_spec addr r.guest_base hle)
    unfold GuestAddress.OffsetFromOutcome at hdv
    have hov := u64_add_overflow r.obj_offset delta (by omega)
    rw [hfind, ho, hc]
    simp only [bind_ok, uncurry, core.option.Option.ok_or, core.result.Result.map,
      offset_from_base.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0MemoryRegionPairShared1PU64.call_once,
      MemoryRegion.start, hd, hdelta, hov]
    simp

/-- `m` is the last element of `l` with a maximal key: no element has a larger
    key, and every element after `m` has a smaller one. -/
def _root_.List.IsLastMaxBy {T : Type} (key : T → Nat) (l : List T) (m : T) : Prop :=
  ∃ pre post, l = pre ++ m :: post ∧ (∀ y ∈ l, key y ≤ key m) ∧ ∀ y ∈ post, key y < key m

theorem _root_.List.IsLastMaxBy.singleton {T : Type} (key : T → Nat) (x : T) :
    [x].IsLastMaxBy key x :=
  ⟨[], [], rfl, by simp, by simp⟩

/-- One step of `max_by_key`: `x` is kept against the next element `y` only if
    its key is strictly larger. -/
theorem _root_.List.IsLastMaxBy.cons_cons {T : Type} {key : T → Nat} {x y m : T}
    {rest : List T} (h : ((if key y < key x then x else y) :: rest).IsLastMaxBy key m) :
    (x :: y :: rest).IsLastMaxBy key m := by
  obtain ⟨pre, post, hl, hle, hlt⟩ := h
  by_cases hxy : key y < key x
  · simp only [hxy, ↓reduceIte] at hl hle
    have hx := hle x (by simp)
    cases pre with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨[], y :: rest, rfl, ?_, ?_⟩
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | rfl | hz
        · exact le_refl _
        · omega
        · exact hle z (by simp [hz])
      · intro z hz
        simp only [List.mem_cons] at hz
        rcases hz with rfl | hz
        · exact hxy
        · exact hlt z hz
    | cons p pre =>
      simp only [List.cons_append, List.cons.injEq] at hl
      obtain ⟨rfl, rfl⟩ := hl
      refine ⟨x :: y :: pre, post, rfl, ?_, hlt⟩
      intro z hz
      simp only [List.mem_cons] at hz
      rcases hz with rfl | rfl | hz
      · exact hx
      · omega
      · exact hle z (by simp [hz])
  · simp only [hxy, ↓reduceIte] at hl hle
    have hy := hle y (by simp)
    refine ⟨x :: pre, post, by simp [hl], ?_, hlt⟩
    intro z hz
    simp only [List.mem_cons] at hz
    rcases hz with rfl | hz
    · omega
    · exact hle z (List.mem_cons.mpr hz)

/-- The `max_by_key` loop over a slice iterator, with a pure key closure `g`
    and a comparison that agrees with `key`, returns the last element of `x`
    followed by the remaining elements that has a maximal key. -/
theorem _root_.core.iter.traits.iterator.Iterator.maxByKeyFrom_slice_spec {T F B : Type}
    (ordInst : core.cmp.Ord B) (fInst : core.ops.function.FnMut F T B) (f : F) (g : T → B)
    (key : B → Nat) (hf : ∀ x, fInst.call_mut f x = ok (g x, f))
    (hcmp : ∀ a b, ordInst.cmp a b ⦃ o => o = .gt ↔ key b < key a ⦄) (s : Slice T) :
    ∀ (i : Nat) (x : T),
      core.iter.traits.iterator.Iterator.maxByKeyFrom
          (core.iter.traits.iterator.IteratorSliceIter T) ordInst fInst (g x, x) ⟨s, i⟩ f
        ⦃ r => ∃ m, r = some m ∧ (x :: s.val.drop i).IsLastMaxBy (fun y => key (g y)) m ⦄ := by
  suffices ∀ n (i : Nat) (x : T), s.val.length - i = n →
      core.iter.traits.iterator.Iterator.maxByKeyFrom
          (core.iter.traits.iterator.IteratorSliceIter T) ordInst fInst (g x, x) ⟨s, i⟩ f
        ⦃ r => ∃ m, r = some m ∧ (x :: s.val.drop i).IsLastMaxBy (fun y => key (g y)) m ⦄ from
    fun i x => this _ i x rfl
  intro n
  induction n with
  | zero =>
    intro i x hn
    have hge : s.val.length ≤ i := by omega
    rw [core.iter.traits.iterator.Iterator.maxByKeyFrom.eq_def]
    simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, Nat.not_lt.mpr hge,
      ↓reduceDIte, bind_ok, WP.spec_ok, List.drop_eq_nil_of_le hge]
    exact ⟨x, rfl, List.IsLastMaxBy.singleton _ x⟩
  | succ n ih =>
    intro i x hn
    have hlt : i < s.val.length := by omega
    have hdrop : s.val.drop i = s.val[i] :: s.val.drop (i + 1) := List.drop_eq_getElem_cons hlt
    rw [core.iter.traits.iterator.Iterator.maxByKeyFrom.eq_def]
    simp only [sliceIter_next_of_lt s i hlt, bind_ok, hf]
    apply WP.spec_bind (hcmp (g x) (g s.val[i]))
    intro o ho
    by_cases hgt : o = .gt
    · simp only [hgt, ↓reduceIte]
      have hk : key (g s.val[i]) < key (g x) := ho.mp hgt
      apply WP.spec_mono (ih (i + 1) x (by omega))
      rintro r ⟨m, rfl, hm⟩
      refine ⟨m, rfl, ?_⟩
      rw [hdrop]
      apply List.IsLastMaxBy.cons_cons
      simpa [hk] using hm
    · simp only [hgt, ↓reduceIte]
      have hk : ¬ key (g s.val[i]) < key (g x) := fun h => hgt (ho.mpr h)
      apply WP.spec_mono (ih (i + 1) s.val[i] (by omega))
      rintro r ⟨m, rfl, hm⟩
      refine ⟨m, rfl, ?_⟩
      rw [hdrop]
      apply List.IsLastMaxBy.cons_cons
      simpa [hk] using hm

/-- `max_by_key` over a slice iterator returns `None` exactly when no elements
    remain, and otherwise the last remaining element with a maximal key. -/
theorem _root_.core.iter.traits.iterator.Iterator.max_by_key_slice_spec {T F B : Type}
    (ordInst : core.cmp.Ord B) (fInst : core.ops.function.FnMut F T B) (f : F) (g : T → B)
    (key : B → Nat) (hf : ∀ x, fInst.call_mut f x = ok (g x, f))
    (hcmp : ∀ a b, ordInst.cmp a b ⦃ o => o = .gt ↔ key b < key a ⦄) (s : Slice T) (i : Nat) :
    core.iter.traits.iterator.Iterator.max_by_key.default
        (core.iter.traits.iterator.IteratorSliceIter T) ordInst fInst ⟨s, i⟩ f
      ⦃ r => match r with
        | none => s.val.drop i = []
        | some m => (s.val.drop i).IsLastMaxBy (fun y => key (g y)) m ⦄ := by
  unfold core.iter.traits.iterator.Iterator.max_by_key.default
  by_cases hlt : i < s.val.length
  · have hdrop : s.val.drop i = s.val[i] :: s.val.drop (i + 1) := List.drop_eq_getElem_cons hlt
    simp only [sliceIter_next_of_lt s i hlt, bind_ok, hf]
    apply WP.spec_mono (core.iter.traits.iterator.Iterator.maxByKeyFrom_slice_spec ordInst fInst
      f g key hf hcmp s (i + 1) s.val[i])
    rintro r ⟨m, rfl, hm⟩
    show (s.val.drop i).IsLastMaxBy _ m
    rw [hdrop]
    exact hm
  · have hge : s.val.length ≤ i := by omega
    simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, hlt, ↓reduceDIte, bind_ok,
      WP.spec_ok, List.drop_eq_nil_of_le hge]

/-! ### `end_addr` -/

/-- The endpoint, as computed by `MemoryRegion::end`, of the last region with
    a maximal start, or address 0 without regions. -/
def EndAddrOutcome (self : GuestMemory) (result : GuestAddress) : Prop :=
  if self.regionList = [] then result = 0#u64
  else ∃ r, self.regionList.IsLastMaxBy (fun r => r.guest_base.val) r ∧ r.EndOutcome result

@[step]
theorem end_addr_spec (self : GuestMemory) :
    self.end_addr ⦃ r => self.EndAddrOutcome r ⦄ := by
  unfold end_addr
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  have hf : ∀ r : MemoryRegion,
      end_addr.closure.Insts.CoreOpsFunctionFnMutTupleShared1Shared0MemoryRegionGuestAddress.call_mut
        () r = ok (r.guest_base, ()) := by
    intro r
    simp [end_addr.closure.Insts.CoreOpsFunctionFnMutTupleShared1Shared0MemoryRegionGuestAddress.call_mut,
      MemoryRegion.start]
  have hcmp : ∀ a b : GuestAddress,
      guest_address.GuestAddress.Insts.CoreCmpOrd.cmp a b ⦃ o => o = .gt ↔ b.val < a.val ⦄ := by
    intro a b
    apply WP.spec_mono (GuestAddress.cmp_spec a b)
    intro o ho
    exact ho.2.2
  apply WP.spec_bind (core.iter.traits.iterator.Iterator.max_by_key_slice_spec _ _ () _ _ hf hcmp
    self.regions.val 0)
  intro o ho
  unfold EndAddrOutcome
  cases o with
  | none =>
    simp only [List.drop_zero] at ho
    simp [ho, core.option.Option.map_or]
  | some m =>
    simp only [List.drop_zero] at ho
    have hne : self.regionList ≠ [] := by
      obtain ⟨pre, post, hl, -⟩ := ho
      simp [regionList, hl]
    simp only [hne, ↓reduceIte, core.option.Option.map_or,
      P.Insts.CoreOpsFunctionFnOnceTupleShared0MemoryRegionGuestAddress.call_once]
    apply WP.spec_mono (MemoryRegion.end_spec m)
    intro r hr
    exact ⟨m, ho, hr⟩

/-- For well-formed memory, `end_addr` is the exclusive end of the last region,
    or 0 without regions. -/
theorem WellFormed.endAddr_val {self : GuestMemory} (h : self.WellFormed) {result : GuestAddress}
    (hOut : self.EndAddrOutcome result) :
    result.val = match self.regionList.getLast? with
      | none => 0
      | some r => r.guest_base.val + r.mapping.length.val := by
  unfold EndAddrOutcome at hOut
  split at hOut
  · rename_i hnil
    simp [hnil, hOut]
  · obtain ⟨r, ⟨pre, post, hl, -, hlt⟩, hend⟩ := hOut
    have hpost : post = [] := by
      cases post with
      | nil => rfl
      | cons y post =>
        have hs := h.sorted
        rw [hl, List.pairwise_append] at hs
        have h1 : r.guest_base.val ≤ y.guest_base.val :=
          List.rel_of_pairwise_cons hs.2.1 (List.mem_cons_self (a := y) (l := post))
        have h2 : y.guest_base.val < r.guest_base.val := hlt y List.mem_cons_self
        omega
    subst hpost
    have hr : r ∈ self.regionList := by simp [hl]
    rw [hl, List.getLast?_append_of_ne_nil _ (by simp)]
    simpa using hend.val_eq_of_valid (h.validBounds hr)

/-! ### `from_regions` -/

/-- The regions sorted stably by guest base, as `from_regions` sorts them. -/
def sortedByBase (regions : List MemoryRegion) : List MemoryRegion :=
  regions.mergeSort (fun a b => a.guest_base.val ≤ b.guest_base.val)

open Classical in
/-- The error for the first rejected region `r`, after the accepted regions
    `pre`. The first region, and a region that starts before an earlier region
    ends, give an overlap. Any other rejected region has an unrepresentable end,
    which the error carries. -/
def RejectionError (pre : List MemoryRegion) (r : MemoryRegion)
    (e : vm_memory.guest_memory.Error) : Prop :=
  if pre = [] ∨ ∃ x ∈ pre, ¬ x.EndsBefore r then e = .MemoryRegionOverlap
  else ∃ size : U128, size.val = r.guest_base.val + r.mapping.length.val ∧
    e = .MemoryRegionTooLarge size

/-- A `GuestMemory` with exactly these regions, in this order, and no memory
    policy. -/
def Accepted (regions : List MemoryRegion)
    (result : core.result.Result GuestMemory vm_memory.guest_memory.Error) : Prop :=
  ∃ gm : GuestMemory, result = .Ok gm ∧ gm.regionList = regions ∧
    gm.locked = false ∧ gm.use_punchhole_locked = false

open Classical in
/-- The regions are sorted by guest base. At most one region, and well-formed
    regions, are accepted. Otherwise `r` is the first region that breaks
    well-formedness, and the result is its rejection error. -/
def FromRegionsOutcome (regions : alloc.vec.Vec MemoryRegion)
    (result : core.result.Result GuestMemory vm_memory.guest_memory.Error) : Prop :=
  let s := sortedByBase regions.val
  if s.length ≤ 1 ∨ RegionsWellFormed s then Accepted s result
  else ∃ pre r post, s = pre ++ r :: post ∧ RegionsWellFormed pre ∧
    ¬ RegionsWellFormed (pre ++ [r]) ∧ ∃ e, RejectionError pre r e ∧ result = .Err e

/-- The end computed by `guest_base.checked_add(mapping.size() as u64)`. -/
private def checkedEnd (r : MemoryRegion) : Option GuestAddress :=
  U64.checked_add r.guest_base (UScalar.cast .U64 r.mapping.length)

private theorem checkedEnd_eq_none_iff (r : MemoryRegion) :
    checkedEnd r = none ↔ ¬ r.ValidBounds := by
  have h := U64.checked_add_bv_spec r.guest_base (UScalar.cast .U64 r.mapping.length)
  unfold checkedEnd MemoryRegion.ValidBounds
  rw [usize_cast_u64_val] at h
  cases ho : U64.checked_add r.guest_base (UScalar.cast .U64 r.mapping.length) with
  | none => simp only [ho] at h; simp; omega
  | some e => simp only [ho] at h; simp; omega

private theorem checkedEnd_eq_some {r : MemoryRegion} {e : GuestAddress}
    (h : checkedEnd r = some e) : e.val = r.guest_base.val + r.mapping.length.val := by
  have hs := U64.checked_add_bv_spec r.guest_base (UScalar.cast .U64 r.mapping.length)
  unfold checkedEnd at h
  rw [h, usize_cast_u64_val] at hs
  exact hs.2.1

private theorem validBounds_of_checkedEnd {r : MemoryRegion} {e : GuestAddress}
    (h : checkedEnd r = some e) : r.ValidBounds := by
  unfold MemoryRegion.ValidBounds
  rw [← checkedEnd_eq_some h]
  have := e.hBounds
  scalar_tac

private theorem endsBefore_trans {a b c : MemoryRegion} (hab : a.EndsBefore b)
    (hbc : b.EndsBefore c) : a.EndsBefore c := by
  unfold MemoryRegion.EndsBefore at *
  omega

/-- Every region of a well-formed list ending with `y` ends before any region
    that `y` ends before. -/
private theorem RegionsWellFormed.endsBefore_of_last {pre : List MemoryRegion}
    {y r : MemoryRegion} (h : RegionsWellFormed (pre ++ [y])) (hy : y.EndsBefore r) :
    ∀ x ∈ pre ++ [y], x.EndsBefore r := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact endsBefore_trans ((List.pairwise_append.mp h.2).2.2 x hx y (by simp)) hy
  · simp only [List.mem_singleton] at hx
    exact hx ▸ hy

private theorem RegionsWellFormed.snoc {pre : List MemoryRegion} {r : MemoryRegion}
    (h : RegionsWellFormed pre) (hall : ∀ x ∈ pre, x.EndsBefore r) (hv : r.ValidBounds) :
    RegionsWellFormed (pre ++ [r]) := by
  refine ⟨fun x hx => ?_, List.pairwise_append.mpr ⟨h.2, by simp, fun x hx y hy => ?_⟩⟩
  · rcases List.mem_append.mp hx with hx | hx
    · exact h.1 x hx
    · simp only [List.mem_singleton] at hx
      exact hx ▸ hv
  · simp only [List.mem_singleton] at hy
    exact hy ▸ hall x hx

private theorem RegionsWellFormed.of_append {l₁ l₂ : List MemoryRegion}
    (h : RegionsWellFormed (l₁ ++ l₂)) : RegionsWellFormed l₁ :=
  ⟨fun x hx => h.1 x (List.mem_append_left _ hx), (List.pairwise_append.mp h.2).1⟩

private theorem from_regions_compare (a b : MemoryRegion) :
    from_regions.closure.Insts.CoreOpsFunctionFnMutPairShared0MemoryRegionShared1MemoryRegionOrdering.call_mut
      () (a, b) = ok (compare a.guest_base.val b.guest_base.val, ()) := by
  simp only [from_regions.closure.Insts.CoreOpsFunctionFnMutPairShared0MemoryRegionShared1MemoryRegionOrdering.call_mut,
    guest_address.GuestAddress.Insts.CoreCmpOrd.cmp, core.cmp.impls.OrdU64.cmp, bind_ok,
    uncurry]

private theorem usize_cast_u128_val (x : Usize) : (UScalar.cast .U128 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem u64_cast_u128_val (x : U64) : (UScalar.cast .U128 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  simp [UScalarTy.numBits]

/-- What the loop over the sorted regions `s` establishes: either `s` is
    well-formed and accepted, or a first region breaks well-formedness and the
    result is its rejection error. -/
private def ChecksResult (s : List MemoryRegion)
    (result : core.result.Result GuestMemory vm_memory.guest_memory.Error) : Prop :=
  (RegionsWellFormed s ∧ Accepted s result) ∨
  ∃ pre r post, s = pre ++ r :: post ∧ RegionsWellFormed pre ∧
    ¬ RegionsWellFormed (pre ++ [r]) ∧ ∃ e, RejectionError pre r e ∧ result = .Err e

/-- The rejection of region `k + 1` after the well-formed regions `0..k`. -/
private theorem ChecksResult.reject {s : List MemoryRegion} {k : Nat} (hk : k + 1 < s.length)
    (hpre : RegionsWellFormed (s.take (k + 1)))
    (hnot : ¬ RegionsWellFormed (s.take (k + 1) ++ [s[k + 1]]))
    {e result} (he : RejectionError (s.take (k + 1)) s[k + 1] e) (hres : result = .Err e) :
    ChecksResult s result := by
  have hsplit : s = s.take (k + 1) ++ s[k + 1] :: s.drop (k + 2) := by
    conv_lhs => rw [← List.take_append_drop (k + 1) s, List.drop_eq_getElem_cons hk]
  exact Or.inr ⟨_, _, _, hsplit, hpre, hnot, e, he, hres⟩

/-- The loop over the regions after the first, at the region after `k`: the
    regions up to `k` are well-formed, and `prevEnd` is the end of region `k`. It
    is stated for any loop body `F` that runs `from_regions_loop.body`. -/
private theorem from_regions_loop_spec (s : List MemoryRegion)
    (regions : alloc.vec.Vec MemoryRegion) (hregions : regions.val = s)
    (s2 : Slice MemoryRegion) (hs2 : s2.val = s.drop 1)
    (F : core.slice.iter.Iter MemoryRegion × GuestAddress →
      Result (ControlFlow (core.slice.iter.Iter MemoryRegion × GuestAddress)
        (core.result.Result GuestMemory vm_memory.guest_memory.Error)))
    (hF : ∀ it prevEnd, F (it, prevEnd) = from_regions_loop.body regions it prevEnd) :
    ∀ (k : Nat) (hk : k < s.length) (prevEnd : GuestAddress),
      RegionsWellFormed (s.take (k + 1)) →
      prevEnd.val = s[k].guest_base.val + s[k].mapping.length.val →
      loop F (⟨s2, k⟩, prevEnd) ⦃ result => ChecksResult s result ⦄ := by
  suffices ∀ n (k : Nat) (hk : k < s.length) (prevEnd : GuestAddress), s.length - k = n →
      RegionsWellFormed (s.take (k + 1)) →
      prevEnd.val = s[k].guest_base.val + s[k].mapping.length.val →
      loop F (⟨s2, k⟩, prevEnd) ⦃ result => ChecksResult s result ⦄ from
    fun k hk prevEnd => this _ k hk prevEnd rfl
  intro n
  induction n with
  | zero =>
    intro k hk _ hn
    omega
  | succ n ih =>
    intro k hk prevEnd hn hpre hprev
    have hs2len : s2.val.length = s.length - 1 := by rw [hs2, List.length_drop]
    have hlastk : s.take (k + 1) = s.take k ++ [s[k]] := List.take_succ_eq_append_getElem hk
    by_cases hnext : k + 1 < s.length
    · have hlt : k < s2.val.length := by omega
      have hget : s2.val[k] = s[k + 1] := by
        simp only [hs2, List.getElem_drop, Nat.add_comm]
      have htake : s.take (k + 1 + 1) = s.take (k + 1) ++ [s[k + 1]] :=
        List.take_succ_eq_append_getElem hnext
      rw [loop.eq_def, hF]
      simp only [from_regions_loop.body, sliceIter_next_of_lt s2 k hlt, bind_ok, uncurry, hget]
      step as ⟨b, hb⟩
      by_cases hover : s[k + 1].guest_base.val < prevEnd.val
      · have hbt : b = true := hb.mpr hover
        simp only [hbt, ↓reduceIte, bind_ok, WP.spec_ok]
        have hnot : ¬ s[k].EndsBefore s[k + 1] := by
          unfold MemoryRegion.EndsBefore
          omega
        have hmem : s[k] ∈ s.take (k + 1) := by
          rw [hlastk]
          exact List.mem_append_right _ (List.mem_singleton_self _)
        apply ChecksResult.reject hnext hpre ?_ ?_ rfl
        ·
          exact fun hwf => hnot ((List.pairwise_append.mp hwf.2).2.2 _ hmem _ (by simp))
        · unfold RejectionError
          rw [ite_eq_left (Or.inr ⟨s[k], hmem, hnot⟩)]
      · have hbf : b = false := by
          cases b
          · rfl
          · exact absurd (hb.mp rfl) hover
        have hends : s[k].EndsBefore s[k + 1] := by
          unfold MemoryRegion.EndsBefore
          omega
        have hall : ∀ x ∈ s.take (k + 1), x.EndsBefore s[k + 1] := by
          rw [hlastk]
          exact RegionsWellFormed.endsBefore_of_last (hlastk ▸ hpre) hends
        simp only [hbf, Bool.false_eq_true, ↓reduceIte,
          base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, lift, bind_ok]
        step as ⟨o1, ho1⟩
        have hb128 : (UScalar.cast .U128 s[k + 1].guest_base).val +
            (UScalar.cast .U128 s[k + 1].mapping.length).val ≤ U128.max := by
          rw [u64_cast_u128_val, usize_cast_u128_val]
          have h0 : s[k + 1].guest_base.val < 2 ^ 64 := by
            have := s[k + 1].guest_base.hBounds
            simpa [UScalarTy.numBits] using this
          have h1 : s[k + 1].mapping.length.val < 2 ^ 64 := by
            rw [← usize_cast_u64_val]
            have := (UScalar.cast .U64 s[k + 1].mapping.length).hBounds
            simpa [UScalarTy.numBits] using this
          rw [U128.max_eq]
          omega
        step as ⟨size, hsize⟩
        have hsizev : size.val = s[k + 1].guest_base.val + s[k + 1].mapping.length.val := by
          rw [hsize, u64_cast_u128_val, usize_cast_u128_val]
        cases hc : checkedEnd s[k + 1] with
        | none =>
          have hon : o1 = none := by rw [ho1]; exact hc
          subst hon
          simp only [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
          apply ChecksResult.reject hnext hpre ?_ ?_ rfl
          ·
            exact fun hwf => (checkedEnd_eq_none_iff _).mp hc (hwf.1 _ (List.mem_append_right _ (List.mem_singleton_self _)))
          · unfold RejectionError
            rw [ite_eq_right]
            · exact ⟨size, hsizev, rfl⟩
            · rintro (h | ⟨x, hx, hn⟩)
              · rw [hlastk] at h
                exact List.append_ne_nil_of_right_ne_nil _ (List.cons_ne_nil _ _) h
              · exact hn (hall x hx)
        | some regionEnd =>
          have hos : o1 = some regionEnd := by rw [ho1]; exact hc
          subst hos
          simp only [core.option.Option.ok_or,
            core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
          apply ih (k + 1) hnext regionEnd (by omega) ?_ (checkedEnd_eq_some hc)
          rw [htake]
          exact hpre.snoc hall (validBounds_of_checkedEnd hc)
    · have hge : s2.val.length ≤ k := by omega
      have hall : s.take (k + 1) = s := List.take_of_length_le (by omega)
      rw [loop.eq_def, hF]
      simp only [from_regions_loop.body, core.slice.iter.IteratorSliceIter.next, Slice.len_val,
        Nat.not_lt.mpr hge, ↓reduceDIte, bind_ok, uncurry,
        alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from, WP.spec_ok]
      exact Or.inl ⟨hall ▸ hpre, _, rfl, hregions, rfl, rfl⟩

/-- With at least two regions, `ChecksResult` establishes the outcome. -/
private theorem ChecksResult.outcome {regions : alloc.vec.Vec MemoryRegion}
    {s : List MemoryRegion} (hs : sortedByBase regions.val = s) (h2 : 1 < s.length) {result}
    (h : ChecksResult s result) : FromRegionsOutcome regions result := by
  subst hs
  simp only [FromRegionsOutcome]
  rcases h with ⟨hwf, hacc⟩ | ⟨pre, r, post, hsp, hpre, hnot, hrest⟩
  · rw [ite_eq_left (Or.inr hwf)]
    exact hacc
  · rw [ite_eq_right]
    · exact ⟨pre, r, post, hsp, hpre, hnot, hrest⟩
    · rintro (hc | hwf)
      · omega
      · have happ : (pre ++ [r]) ++ post = sortedByBase regions.val := by rw [hsp]; simp
        rw [← happ] at hwf
        exact hnot hwf.of_append

@[step]
theorem from_regions_spec (regions : alloc.vec.Vec MemoryRegion) :
    from_regions regions ⦃ result => FromRegionsOutcome regions result ⦄ := by
  unfold from_regions
  simp only [lift, alloc.vec.Vec.deref_mut, bind_ok, uncurry]
  step with alloc.slice.Slice.sort_by_key_spec
    from_regions.closure.Insts.CoreOpsFunctionFnMutPairShared0MemoryRegionShared1MemoryRegionOrdering
    () (fun r => r.guest_base.val) from_regions_compare regions.slice as ⟨sorted, hsorted⟩
  have hs : sortedByBase regions.val = sorted.val := hsorted.symm
  have hlenv : (alloc.vec.Vec.len ({ slice := sorted } : alloc.vec.Vec MemoryRegion)).val =
      sorted.val.length := alloc.vec.Vec.len_val _
  by_cases hlen : 1 < sorted.val.length
  · have hgt : alloc.vec.Vec.len ({ slice := sorted } : alloc.vec.Vec MemoryRegion) > 1#usize := by
      scalar_tac
    simp only [hgt, ↓reduceIte]
    refine WP.spec_mono (P₀ := ChecksResult sorted.val) ?_ (fun _ h => h.outcome hs hlen)
    step as ⟨mr, hmr⟩
    have hmr' : mr = sorted.val[0] := by simpa [alloc.vec.Vec.val] using hmr
    subst hmr'
    simp only [base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, bind_ok]
    step as ⟨o, ho⟩
    cases hc : checkedEnd sorted.val[0] with
    | none =>
      have hon : o = none := by rw [ho]; exact hc
      subst hon
      simp only [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      refine Or.inr ⟨[], sorted.val[0], sorted.val.drop 1, ?_, ⟨by simp, by simp⟩, ?_,
        .MemoryRegionOverlap, ?_, rfl⟩
      · rw [List.nil_append]
        exact List.drop_eq_getElem_cons (l := sorted.val) (i := 0) (by omega)
      · exact fun hwf => (checkedEnd_eq_none_iff _).mp hc (hwf.1 _ (by simp))
      · unfold RejectionError
        rw [ite_eq_left (Or.inl rfl)]
    | some firstEnd =>
      have hos : o = some firstEnd := by rw [ho]; exact hc
      subst hos
      simp only [core.option.Option.ok_or,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step as ⟨s2, hs2, _⟩
      step as ⟨it, hit1, hit2⟩
      have hit : it = ⟨s2, 0⟩ := by
        cases it
        simp_all
      subst hit
      have hs2v : s2.val = sorted.val.drop 1 := by simpa [alloc.vec.Vec.val] using hs2
      unfold from_regions_loop
      refine from_regions_loop_spec sorted.val { slice := sorted } rfl s2 hs2v _ ?_ 0
        (by omega) firstEnd ?_ (checkedEnd_eq_some hc)
      · intro _ _
        rfl
      · rw [List.take_succ_eq_append_getElem (by omega), List.take_zero, List.nil_append]
        exact ⟨by simpa using validBounds_of_checkedEnd hc, by simp⟩
  · have hle : ¬ alloc.vec.Vec.len ({ slice := sorted } : alloc.vec.Vec MemoryRegion) > 1#usize := by
      scalar_tac
    simp only [hle, ↓reduceIte, WP.spec_ok, FromRegionsOutcome]
    rw [ite_eq_left (Or.inl (show (sortedByBase regions.val).length ≤ 1 by rw [hs]; omega))]
    exact ⟨_, rfl, hs.symm, rfl, rfl⟩

private theorem eq_of_regionList {a b : GuestMemory} (h : a.regionList = b.regionList)
    (hl : a.locked = b.locked) (hp : a.use_punchhole_locked = b.use_punchhole_locked) : a = b := by
  obtain ⟨⟨sa⟩, _, _⟩ := a
  obtain ⟨⟨sb⟩, _, _⟩ := b
  have : sa = sb := Slice.ext sa sb h
  simp_all

/-- With at least two regions, `from_regions` returns `gm` exactly when `gm`
    holds the regions sorted by guest base, has no memory policy, and is
    well-formed. -/
theorem FromRegionsOutcome.eq_ok_iff {regions : alloc.vec.Vec MemoryRegion} {result}
    (hOut : FromRegionsOutcome regions result) (h2 : 1 < regions.val.length) (gm : GuestMemory) :
    result = .Ok gm ↔ gm.regionList = sortedByBase regions.val ∧ gm.locked = false ∧
      gm.use_punchhole_locked = false ∧ gm.WellFormed := by
  have hlen : 1 < (sortedByBase regions.val).length := by simpa [sortedByBase] using h2
  unfold FromRegionsOutcome at hOut
  simp only at hOut
  generalize sortedByBase regions.val = s at hOut hlen ⊢
  split at hOut
  · rename_i hc
    have hwf : RegionsWellFormed s := hc.resolve_left (by omega)
    obtain ⟨gm', rfl, hl, hlk, hp⟩ := hOut
    simp only [core.result.Result.Ok.injEq]
    constructor
    · rintro rfl
      exact ⟨hl, hlk, hp, by unfold WellFormed; rw [hl]; exact hwf⟩
    · rintro ⟨hl', hlk', hp', -⟩
      exact eq_of_regionList (hl.trans hl'.symm) (hlk.trans hlk'.symm) (hp.trans hp'.symm)
  · rename_i hc
    obtain ⟨_, _, _, _, _, _, e, _, rfl⟩ := hOut
    simp only [reduceCtorEq, false_iff, not_and]
    intro hl _ _ hwf
    unfold WellFormed at hwf
    exact hc (Or.inr (hl ▸ hwf))

end vm_memory.guest_memory.GuestMemory
