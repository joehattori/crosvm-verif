module
public import Syscalls.Mmap
public import Utils.Alignment
@[expose] public section
open Aeneas Aeneas.Std Result
open Utils.Alignment

namespace Syscalls.Mmap

abbrev Mapping := vm_memory.base.sys.linux.mmap.MemoryMapping

/-- Mapped bytes tracked within one reservation. This is ghost state, not the
    Rust `MemoryMapping` record or a model of all process mappings. -/
abbrev MappingState := Nat → Prop

def intervalState (start stop : Nat) : MappingState :=
  fun p => start ≤ p ∧ p < stop

def Mapping.state (m : Mapping) : MappingState :=
  intervalState m.addr.addr.val (m.addr.addr.val + m.size.val)

def MappingState.Covers (s : MappingState) (m : Mapping) : Prop :=
  ∀ p, m.state p → s p

/-- Trusted effect model for ordinary Linux pages: successful `munmap` removes
    all pages intersecting the range; a failed trim preserves the tracked state.
    Successful calls must start on a page boundary (see `MunmapSpec`). The model
    only tracks bytes of the reservation, not unrelated mappings or permissions. -/
def unmapEffect (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) (ret : I32) : MappingState :=
  if ret = 0#i32 then
    fun p => before p ∧
      (p < addr.addr.val ∨ alignUp (addr.addr.val + len.val) pageSize.val ≤ p)
  else before

/-- A syscall contract with an explicit before/after mapped state. -/
def MunmapCallSpec (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) (ret : I32) (after : MappingState) : Prop :=
  MunmapReturnSpec pageSize addr len ret ∧
  after = unmapEffect pageSize before addr len ret

/-- Stateful instrumentation of the actual external call. The C result is
    preserved; the second component records the syscall's modeled effect. -/
def munmapWithState (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) : Result (I32 × MappingState) := do
  let ret ← _root_.libc_1.unix.munmap addr len
  ok (ret, unmapEffect pageSize before addr len ret)

@[step]
theorem munmapWithState_spec (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize)
    (hcall : ∃ ret, MunmapReturnSpec pageSize addr len ret) :
    munmapWithState pageSize before addr len ⦃ ret after =>
      MunmapCallSpec pageSize before addr len ret after ⦄ := by
  obtain ⟨ret, hret⟩ := hcall
  simp only [munmapWithState, hret.1, bind_ok, WP.spec_ok]
  exact ⟨hret, rfl⟩

theorem munmapWithState_erase (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) :
    (do let (ret, _) ← munmapWithState pageSize before addr len; ok ret) =
      _root_.libc_1.unix.munmap addr len := by
  simp [munmapWithState, Std.bind_pure]

theorem unmapEffect_failure (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) (ret : I32) (h : ret ≠ 0#i32) :
    unmapEffect pageSize before addr len ret = before := by
  simp [unmapEffect, h]

/-- Removing a prefix `[a,c)` leaves `[c,b)`, represented by another existing
    `MemoryMapping` record. The cut must be page aligned. -/
theorem unmapEffect_prefix (pageSize : Usize) (before after : Mapping)
    (len : Usize)
    (hstart : before.addr.addr.val ≤ after.addr.addr.val)
    (hlen : before.addr.addr.val + len.val = after.addr.addr.val)
    (hend : before.addr.addr.val + before.size.val = after.addr.addr.val + after.size.val)
    (halign : after.addr.addr.val % pageSize.val = 0) :
    unmapEffect pageSize before.state (RawPtr.cast _ .Mut before.addr) len 0#i32 =
      after.state := by
  funext p
  apply propext
  simp only [unmapEffect, ↓reduceIte, Mapping.state, intervalState, RawPtr.cast]
  rw [hlen, alignUp, if_pos halign]
  omega

theorem unmapEffect_suffix (pageSize : Usize) (before after : Mapping)
    (addr : VoidPtr) (len : Usize)
    (hstart : before.addr = after.addr)
    (hcut : addr.addr.val = after.addr.addr.val + after.size.val)
    (hend : addr.addr.val + len.val = before.addr.addr.val + before.size.val)
    (hsize : after.size.val ≤ before.size.val) :
    unmapEffect pageSize before.state addr len 0#i32 = after.state := by
  have hround := le_alignUp (addr.addr.val + len.val) pageSize.val
  funext p
  apply propext
  simp only [unmapEffect, ↓reduceIte, Mapping.state, intervalState]
  rw [hstart] at hend ⊢
  omega

/-- A trim outside the kept bytes preserves their mapping, including the
    page-rounded effect at the end of a prefix. -/
theorem unmapEffect_covers (pageSize : Usize) (before : MappingState)
    (kept : Mapping) (addr : VoidPtr) (len : Usize) (ret : I32)
    (hpage : 0 < pageSize.val)
    (halign : kept.addr.addr.val % pageSize.val = 0)
    (hbefore : before.Covers kept)
    (hdisjoint : addr.addr.val + len.val ≤ kept.addr.addr.val ∨
      kept.addr.addr.val + kept.size.val ≤ addr.addr.val) :
    (unmapEffect pageSize before addr len ret).Covers kept := by
  intro p hp
  by_cases hret : ret = 0#i32
  · simp only [unmapEffect, hret, ↓reduceIte]
    refine ⟨hbefore p hp, ?_⟩
    change kept.addr.addr.val ≤ p ∧ p < kept.addr.addr.val + kept.size.val at hp
    rcases hdisjoint with hleft | hright
    · have := alignUp_le hpage halign hleft
      exact Or.inr (by omega)
    · exact Or.inl (by omega)
  · simpa [unmapEffect, hret] using hbefore p hp

structure TrimmedMapping where
  mapping : Mapping
  remaining : MappingState
  /-- All nonempty trim calls returned zero; skipped calls need no cleanup. -/
  cleaned : Bool

/-- Ghost-state instrumentation of the prefix/suffix cleanup in
    `try_mmap_populate`. `trimMapping_erase` connects it to the extracted code. -/
def trimMapping (pageSize : Usize) (reservation kept : Mapping) : Result TrimmedMapping := do
  let prefixLen ← kept.addr.addr - reservation.addr.addr
  let first ←
    if prefixLen > 0#usize then do
      let call ← munmapWithState pageSize reservation.state
        (RawPtr.cast _ .Mut reservation.addr) prefixLen
      ok (call.2, call.1 == 0#i32)
    else ok (reservation.state, true)
  let middle := first.1
  let prefixClean := first.2
  let cut ← kept.addr.addr + kept.size
  let stop ← reservation.addr.addr + reservation.size
  let suffix ← stop - cut
  let last ←
    if suffix > 0#usize then do
      let call ← munmapWithState pageSize middle
        (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut cut) suffix
      ok (call.2, call.1 == 0#i32)
    else ok (middle, true)
  ok { mapping := kept, remaining := last.1, cleaned := prefixClean && last.2 }

/-- Starting with the reservation mapped, every retained byte remains mapped.
    If every necessary trim succeeds, the
    remaining tracked bytes are exactly those described by `kept`. Failed calls
    retain their bytes, even though the Rust implementation ignores their status. -/
theorem trimMapping_spec (pageSize : Usize) (reservation kept : Mapping)
    (hpage : 0 < pageSize.val)
    (halign : kept.addr.addr.val % pageSize.val = 0)
    (hstart : reservation.addr.addr.val ≤ kept.addr.addr.val)
    (hend : kept.addr.addr.val + kept.size.val ≤ reservation.addr.addr.val + reservation.size.val)
    (hfit : reservation.addr.addr.val + reservation.size.val ≤ Usize.max)
    (hcalls : ∀ addr len,
      IsTrimmedSubrange (RawPtr.cast _ .Mut reservation.addr) reservation.size
        (RawPtr.cast _ .Mut kept.addr) kept.size addr len →
      ∃ ret, MunmapReturnSpec pageSize addr len ret) :
    trimMapping pageSize reservation kept ⦃ out =>
      out.mapping = kept ∧ out.remaining.Covers kept ∧
      (out.cleaned = true → out.remaining = kept.state) ⦄ := by
  have hbefore : reservation.state.Covers kept := by
    intro p hp
    simp only [Mapping.state, intervalState] at hp ⊢
    omega
  unfold trimMapping
  step as ⟨prefixLen, hprefix⟩
  have hpref :
      (if prefixLen > 0#usize then do
        let call ← munmapWithState pageSize reservation.state
          (RawPtr.cast _ .Mut reservation.addr) prefixLen
        ok (call.2, call.1 == 0#i32)
      else ok (reservation.state, true)) ⦃ middle clean =>
        middle.Covers kept ∧ (clean = true →
          middle = intervalState kept.addr.addr.val
            (reservation.addr.addr.val + reservation.size.val)) ⦄ := by
    by_cases hpos : prefixLen > 0#usize
    · have htrim : IsTrimmedSubrange (RawPtr.cast _ .Mut reservation.addr) reservation.size
          (RawPtr.cast _ .Mut kept.addr) kept.size (RawPtr.cast _ .Mut reservation.addr) prefixLen := by
        simp only [IsTrimmedSubrange, RawPtr.cast]
        exact ⟨by scalar_tac, le_rfl, by omega, Or.inl (by omega)⟩
      obtain ⟨ret, hret⟩ := hcalls _ _ htrim
      simp only [hpos, ↓reduceIte, munmapWithState, hret.1, bind_ok]
      simp only [WP.spec_ok, WP.uncurry'_pair]
      refine ⟨unmapEffect_covers pageSize _ kept _ _ ret hpage halign hbefore htrim.2.2.2, ?_⟩
      intro hzero
      have hz : ret = 0#i32 := by simpa using hzero
      funext p
      apply propext
      have he : reservation.addr.addr.val + prefixLen.val = kept.addr.addr.val := by omega
      simp only [unmapEffect, hz, ↓reduceIte, Mapping.state, intervalState, RawPtr.cast]
      rw [he, alignUp, if_pos halign]
      omega
    · simp only [hpos, ↓reduceIte, WP.spec_ok]
      refine ⟨hbefore, ?_⟩
      intro _
      have he : kept.addr.addr.val = reservation.addr.addr.val := by scalar_tac
      simp only [Mapping.state, he]
  step with hpref as ⟨first, hmiddle, hclean⟩
  obtain ⟨middle, prefixClean⟩ := first
  simp only at hmiddle hclean
  step as ⟨cut, hcut⟩
  step as ⟨stop, hstop⟩
  step as ⟨suffix, hsuffix⟩
  let ptr := RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut cut
  have hptr : ptr.addr.val = cut.val := by simp [ptr, RawPtr.ofUScalar]
  have hsuf :
      (if suffix > 0#usize then do
        let call ← munmapWithState pageSize middle ptr suffix
        ok (call.2, call.1 == 0#i32)
      else ok (middle, true)) ⦃ remaining clean =>
        remaining.Covers kept ∧ ((prefixClean && clean) = true → remaining = kept.state) ⦄ := by
    by_cases hpos : suffix > 0#usize
    · have htrim : IsTrimmedSubrange (RawPtr.cast _ .Mut reservation.addr) reservation.size
          (RawPtr.cast _ .Mut kept.addr) kept.size ptr suffix := by
        simp only [IsTrimmedSubrange, RawPtr.cast]
        exact ⟨by scalar_tac, by omega, by omega, Or.inr (by omega)⟩
      obtain ⟨ret, hret⟩ := hcalls _ _ htrim
      simp only [hpos, ↓reduceIte, munmapWithState, hret.1, bind_ok]
      simp only [WP.spec_ok, WP.uncurry'_pair]
      refine ⟨unmapEffect_covers pageSize _ kept _ _ ret hpage halign hmiddle htrim.2.2.2, ?_⟩
      intro hzero
      obtain ⟨hfirst, hlast⟩ := Bool.and_eq_true_iff.mp hzero
      have hz : ret = 0#i32 := by simpa using hlast
      have hm := hclean hfirst
      have hround := le_alignUp (ptr.addr.val + suffix.val) pageSize.val
      funext p
      apply propext
      simp only [unmapEffect, hz, ↓reduceIte, hm, Mapping.state, intervalState]
      omega
    · simp only [hpos, ↓reduceIte, WP.spec_ok]
      refine ⟨hmiddle, ?_⟩
      intro hfirst
      have hm := hclean (by simpa using hfirst)
      have he : reservation.addr.addr.val + reservation.size.val = kept.addr.addr.val + kept.size.val := by scalar_tac
      simpa only [Mapping.state, he] using hm
  step with hsuf as ⟨last, hremaining, hcleaned⟩
  obtain ⟨remaining, suffixClean⟩ := last
  exact ⟨hremaining, hcleaned⟩

private theorem bind_ite {α β : Type} (p : Prop) [Decidable p]
    (yes no : Result α) (f : α → Result β) :
    Std.bind (if p then yes else no) f =
      if p then Std.bind yes f else Std.bind no f := by
  split <;> rfl

/-- Erasing the ghost state gives precisely the cleanup computation used by the
    translated function. No successful syscall assumption is needed here. -/
theorem trimMapping_erase (pageSize : Usize) (reservation kept : Mapping) :
    (do let out ← trimMapping pageSize reservation kept; ok out.mapping) =
    (do
      let prefixLen ← kept.addr.addr - reservation.addr.addr
      let _ ←
        if prefixLen > 0#usize then do
          let _ ← _root_.libc_1.unix.munmap (RawPtr.cast _ .Mut reservation.addr) prefixLen
          ok ()
        else ok ()
      let cut ← kept.addr.addr + kept.size
      let stop ← reservation.addr.addr + reservation.size
      let suffix ← stop - cut
      let _ ←
        if suffix > 0#usize then do
          let _ ← _root_.libc_1.unix.munmap
            (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut cut) suffix
          ok ()
        else ok ()
      ok kept) := by
  simp [trimMapping, munmapWithState, bind_tc_eq, Std.bind_assoc, bind_ite]

end Syscalls.Mmap
