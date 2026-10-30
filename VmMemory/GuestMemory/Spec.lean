module
public import VmMemory.MemoryRegion.Spec
import all Aeneas.Std.Scalar.Ops.Add
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address

namespace vm_memory.guest_memory.GuestMemory

/-- The regions in slice order. -/
abbrev regionList (self : GuestMemory) : List MemoryRegion := self.regions.val.val

/-- Well-formed guest memory: every region's exclusive end is representable, and
    each region ends at or before every later region starts. -/
def WellFormed (self : GuestMemory) : Prop :=
  (∀ r ∈ self.regionList, r.ValidBounds) ∧ self.regionList.Pairwise MemoryRegion.EndsBefore

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

/-! ### `find_region` -/

open Classical in
/-- The first region whose `contains` accepts the address yields its mapping,
    the address's offset from the region start cast to `usize`, and its object
    offset. If no region accepts it, the error carries the address. -/
def FindRegionOutcome (self : GuestMemory) (addr : GuestAddress)
    (result : core.result.Result (base.mmap.MemoryMapping × Usize × U64)
      vm_memory.guest_memory.Error) : Prop :=
  match self.regionList.find? (fun r => decide (r.ContainsOutcome addr true)) with
  | none => result = .Err (.InvalidGuestAddress addr)
  | some r => ∃ offset, GuestAddress.OffsetFromOutcome addr r.guest_base offset ∧
      result = .Ok (r.mapping, UScalar.cast .Usize offset, r.obj_offset)

@[step]
theorem find_region_spec (self : GuestMemory) (addr : GuestAddress) :
    self.find_region addr ⦃ r => self.FindRegionOutcome addr r ⦄ := by
  classical
  unfold find_region
  simp only [alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref, core.slice.Slice.iter, bind_ok]
  have hf : ∀ r,
      find_region.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared0MemoryRegionBool.call_mut
        addr r ⦃ p => p.2 = addr ∧ (p.1 = true ↔ r.ContainsOutcome addr true) ⦄ := by
    intro r
    unfold find_region.closure.Insts.CoreOpsFunctionFnMutTupleShared2Shared0MemoryRegionBool.call_mut
    apply WP.spec_bind (MemoryRegion.contains_spec r addr)
    intro b hb
    simpa using hb.eq_true_iff
  apply WP.spec_bind (core.slice.iter.Iter.find_spec _ _ addr hf _)
  rintro ⟨o, _⟩ ho
  simp only [List.drop_zero] at ho
  subst ho
  unfold FindRegionOutcome
  cases hfind : self.regionList.find? (fun r => decide (r.ContainsOutcome addr true)) with
  | none => simp [core.option.Option.ok_or, core.result.Result.map]
  | some r =>
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    obtain ⟨endAddr, -, hc⟩ := hp
    have hle : r.guest_base.val ≤ addr.val := (hc.mp rfl).1
    simp only [core.option.Option.ok_or, core.result.Result.map,
      find_region.closure_1.Insts.CoreOpsFunctionFnOnceTupleShared0MemoryRegionTupleShared1MemoryMappingUsizeU64.call_once]
    step as ⟨start, hstart⟩
    subst hstart
    step as ⟨offset, hoffset⟩
    simp only [lift, bind_ok, WP.spec_ok]
    exact ⟨offset, hoffset, rfl⟩

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
  classical
  unfold FindRegionOutcome at hOut
  cases hfind : self.regionList.find? (fun r => decide (r.ContainsOutcome addr true)) with
  | none =>
    rw [hfind] at hOut
    subst hOut
    simp only [reduceCtorEq, false_iff, not_exists, not_and]
    intro r hr hin
    have := List.find?_eq_none.mp hfind r hr
    simp only [decide_eq_true_eq] at this
    exact absurd ((containsOutcome_true_iff (h.validBounds hr) addr).mpr hin) this
  | some r =>
    rw [hfind] at hOut
    obtain ⟨o, ho, hres⟩ := hOut
    subst hres
    have hr := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    have hin := (containsOutcome_true_iff (h.validBounds hr) addr).mp hp
    unfold GuestAddress.OffsetFromOutcome at ho
    simp only [core.result.Result.Ok.injEq, Prod.mk.injEq]
    constructor
    · rintro ⟨rfl, rfl, rfl⟩
      exact ⟨r, hr, hin, rfl, by rw [Platform64.u64_cast_usize_val, ho], rfl⟩
    · rintro ⟨r', hr', hin', rfl, hoff, rfl⟩
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hr'
      obtain rfl := h.index_eq_of_mem hi hj hin hin'
      exact ⟨rfl, UScalar.eq_of_val_eq (by rw [Platform64.u64_cast_usize_val, ho, hoff]), rfl⟩

/-- `find_region` fails only with `InvalidGuestAddress` for the given address,
    and for well-formed memory exactly when no region's mathematical half-open
    interval contains it. -/
theorem WellFormed.findRegion_eq_err_iff {self : GuestMemory} (h : self.WellFormed)
    {addr : GuestAddress} {result} (hOut : self.FindRegionOutcome addr result)
    (e : vm_memory.guest_memory.Error) :
    result = .Err e ↔ e = .InvalidGuestAddress addr ∧ ∀ r ∈ self.regionList,
      ¬ (r.guest_base.val ≤ addr.val ∧ addr.val < r.guest_base.val + r.mapping.length.val) := by
  classical
  unfold FindRegionOutcome at hOut
  cases hfind : self.regionList.find? (fun r => decide (r.ContainsOutcome addr true)) with
  | none =>
    rw [hfind] at hOut
    subst hOut
    have hnone := List.find?_eq_none.mp hfind
    simp only [core.result.Result.Err.injEq]
    constructor
    · rintro rfl
      refine ⟨rfl, fun r hr hin => ?_⟩
      have := hnone r hr
      simp only [decide_eq_true_eq] at this
      exact this ((containsOutcome_true_iff (h.validBounds hr) addr).mpr hin)
    · rintro ⟨rfl, -⟩
      rfl
  | some r =>
    rw [hfind] at hOut
    obtain ⟨o, -, hres⟩ := hOut
    subst hres
    have hr := List.mem_of_find?_eq_some hfind
    have hp := List.find?_some hfind
    simp only [decide_eq_true_eq] at hp
    have hin := (containsOutcome_true_iff (h.validBounds hr) addr).mp hp
    simp only [reduceCtorEq, false_iff]
    rintro ⟨-, hall⟩
    exact hall r hr hin

end vm_memory.guest_memory.GuestMemory
