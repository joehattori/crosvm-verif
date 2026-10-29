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

/-- Contract for trimming an allocated region. The input record describes bytes
    mapped in `before`; `after` describes the remaining mapped bytes. A successful
    call removes the page-rounded range and a failed call leaves it unchanged.
    This is a restricted contract for our cleanup calls: Linux also permits
    unmapping ranges that were not mapped, but those calls are outside its scope. -/
structure MunmapCallSpec (pageSize : Usize) (before : MappingState)
    (removed : Mapping) (ret : I32) (after : MappingState) : Prop where
  allocated : before.Covers removed
  return_spec : MunmapReturnSpec pageSize (RawPtr.cast _ .Mut removed.addr) removed.size ret
  effect : after = unmapEffect pageSize before (RawPtr.cast _ .Mut removed.addr) removed.size ret

/-- Trusted syscall contract for allowed, currently mapped regions. Each call
    receives the current allocation state and returns its updated state together
    with the actual C status. Subsequent calls must establish coverage in that
    returned state, not reuse the original reservation's coverage. -/
def MunmapSpec (pageSize : Usize) (allowed : VoidPtr → Usize → Prop) : Prop :=
  ∀ (before : MappingState) (removed : Mapping), before.Covers removed →
    allowed (RawPtr.cast _ .Mut removed.addr) removed.size →
    ∃ ret after, MunmapCallSpec pageSize before removed ret after

/-- Stateful instrumentation of the actual external call. The C result is
    preserved; the second component records the syscall's modeled effect. -/
def munmapWithState (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) : Result (I32 × MappingState) := do
  let ret ← _root_.libc_1.unix.munmap addr len
  ok (ret, unmapEffect pageSize before addr len ret)

@[step]
theorem munmapWithState_spec (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize)
    (hcall : ∃ ret after, MunmapCallSpec pageSize before
      { addr := RawPtr.cast U8 .Mut addr, size := len } ret after) :
    munmapWithState pageSize before addr len ⦃ ret after =>
      MunmapCallSpec pageSize before { addr := RawPtr.cast U8 .Mut addr, size := len }
        ret after ⦄ := by
  obtain ⟨ret, after, hret⟩ := hcall
  have hr : _root_.libc_1.unix.munmap addr len = ok ret := hret.return_spec.1
  simp only [munmapWithState, hr, bind_ok, WP.spec_ok]
  simpa only [hret.effect, WP.uncurry'_pair, RawPtr.cast] using hret

theorem munmapWithState_erase (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) :
    (do let (ret, _) ← munmapWithState pageSize before addr len; ok ret) =
      _root_.libc_1.unix.munmap addr len := by
  simp [munmapWithState, Std.bind_pure]

theorem unmapEffect_failure (pageSize : Usize) (before : MappingState)
    (addr : VoidPtr) (len : Usize) (ret : I32) (h : ret ≠ 0#i32) :
    unmapEffect pageSize before addr len ret = before := by
  simp [unmapEffect, h]

theorem MunmapCallSpec.failure {pageSize : Usize} {before after : MappingState}
    {removed : Mapping} {ret : I32} (h : MunmapCallSpec pageSize before removed ret after)
    (hret : ret ≠ 0#i32) : after = before := by
  rw [h.effect, unmapEffect_failure _ _ _ _ _ hret]

/-- A successful call really removes every requested byte from the mapped state. -/
theorem MunmapCallSpec.removed_unmapped {pageSize : Usize} {before after : MappingState}
    {removed : Mapping} {ret : I32} (h : MunmapCallSpec pageSize before removed ret after)
    (hret : ret = 0#i32) : ∀ p, removed.state p → ¬after p := by
  intro p hp ha
  rw [h.effect] at ha
  have hround := le_alignUp (removed.addr.addr.val + removed.size.val) pageSize.val
  simp only [unmapEffect, hret, ↓reduceIte, RawPtr.cast] at ha
  simp only [Mapping.state, intervalState] at hp
  omega

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

/-- Successful prefix trimming returns the state of the shortened mapping record. -/
theorem MunmapCallSpec.prefix {pageSize : Usize} {original kept : Mapping}
    {len : Usize} {ret : I32} {after : MappingState}
    (h : MunmapCallSpec pageSize original.state { addr := original.addr, size := len } ret after)
    (hret : ret = 0#i32)
    (hstart : original.addr.addr.val ≤ kept.addr.addr.val)
    (hlen : original.addr.addr.val + len.val = kept.addr.addr.val)
    (hend : original.addr.addr.val + original.size.val = kept.addr.addr.val + kept.size.val)
    (halign : kept.addr.addr.val % pageSize.val = 0) : after = kept.state := by
  rw [h.effect, hret]
  exact unmapEffect_prefix pageSize original kept len hstart hlen hend halign

theorem MunmapCallSpec.suffix {pageSize : Usize} {original kept removed : Mapping}
    {ret : I32} {after : MappingState}
    (h : MunmapCallSpec pageSize original.state removed ret after)
    (hret : ret = 0#i32)
    (hstart : original.addr = kept.addr)
    (hcut : removed.addr.addr.val = kept.addr.addr.val + kept.size.val)
    (hend : removed.addr.addr.val + removed.size.val = original.addr.addr.val + original.size.val)
    (hsize : kept.size.val ≤ original.size.val) : after = kept.state := by
  rw [h.effect, hret]
  exact unmapEffect_suffix pageSize original kept (RawPtr.cast _ .Mut removed.addr)
    removed.size hstart hcut hend hsize

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
    (hcalls : MunmapSpec pageSize
      (IsTrimmedSubrange (RawPtr.cast _ .Mut reservation.addr) reservation.size
        (RawPtr.cast _ .Mut kept.addr) kept.size)) :
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
        middle.Covers kept ∧
        (∀ p, intervalState kept.addr.addr.val
          (reservation.addr.addr.val + reservation.size.val) p → middle p) ∧
        (clean = true →
          middle = intervalState kept.addr.addr.val
            (reservation.addr.addr.val + reservation.size.val)) ⦄ := by
    by_cases hpos : prefixLen > 0#usize
    · have htrim : IsTrimmedSubrange (RawPtr.cast _ .Mut reservation.addr) reservation.size
          (RawPtr.cast _ .Mut kept.addr) kept.size (RawPtr.cast _ .Mut reservation.addr) prefixLen := by
        simp only [IsTrimmedSubrange, RawPtr.cast]
        exact ⟨by scalar_tac, le_rfl, by omega, Or.inl (by omega)⟩
      have hallocated : reservation.state.Covers
          { addr := reservation.addr, size := prefixLen } := by
        intro p hp
        simp only [Mapping.state, intervalState] at hp ⊢
        omega
      simp only [hpos, ↓reduceIte]
      step with munmapWithState_spec pageSize reservation.state
        (RawPtr.cast _ .Mut reservation.addr) prefixLen
        (hcalls _ _ hallocated htrim) as ⟨call, hcall⟩
      obtain ⟨ret, after⟩ := call
      simp only at hcall
      rw [hcall.effect]
      have he : reservation.addr.addr.val + prefixLen.val = kept.addr.addr.val := by omega
      refine ⟨unmapEffect_covers pageSize _ kept _ _ ret hpage halign hbefore htrim.2.2.2,
        ?_, ?_⟩
      · intro p hp
        have horig : reservation.state p := by
          simp only [Mapping.state, intervalState] at hp ⊢
          omega
        simp only [unmapEffect]
        split
        · exact ⟨horig, Or.inr (by simpa [RawPtr.cast, he, alignUp, halign] using hp.1)⟩
        · exact horig
      · intro hzero
        have hz : ret = 0#i32 := by simpa using hzero
        funext p
        apply propext
        simp only [unmapEffect, hz, ↓reduceIte, Mapping.state, intervalState, RawPtr.cast]
        rw [he, alignUp, if_pos halign]
        omega
    · simp only [hpos, ↓reduceIte, WP.spec_ok]
      have he : kept.addr.addr.val = reservation.addr.addr.val := by scalar_tac
      refine ⟨hbefore, ?_, ?_⟩
      · simpa only [Mapping.state, he] using (fun p (hp : reservation.state p) => hp)
      · intro _
        simp only [Mapping.state, he]
  step with hpref as ⟨first, hmiddle, htail, hclean⟩
  obtain ⟨middle, prefixClean⟩ := first
  simp only at hmiddle htail hclean
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
      have hallocated : middle.Covers { addr := RawPtr.cast U8 .Mut ptr, size := suffix } := by
        intro p hp
        apply htail p
        simp only [Mapping.state, intervalState, RawPtr.cast] at hp ⊢
        omega
      simp only [hpos, ↓reduceIte]
      step with munmapWithState_spec pageSize middle ptr suffix
        (hcalls _ _ hallocated htrim) as ⟨call, hcall⟩
      obtain ⟨ret, after⟩ := call
      have heffect : after = unmapEffect pageSize middle ptr suffix ret := hcall.effect
      rw [heffect]
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
