module
public import VmMemory.Funs
public import Syscalls.Mmap
public import Utils.Alignment
public import Utils.Platform
import all Init.Data.Nat.Power2.Basic
@[expose] public section
open Aeneas Aeneas.Std Result
open Syscalls.Mmap
open Utils.Alignment
open vm_memory
open vm_memory.base.mmap (Protection)
local notation "MmapError" => vm_memory.base.mmap.Error

namespace base.sys.linux.mmap.MemoryMapping

abbrev PlatformMemoryMapping := vm_memory.base.sys.linux.mmap.MemoryMapping

/-- Mathematical properties of a successful mapping, expressed only in terms
    of the request and the returned value. Memory contents, access permissions,
    ownership, and cleanup are outside this return-value model. -/
structure MappingProperties (pageSize : Usize) (hint_addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (mapping : PlatformMemoryMapping) : Prop where
  size_eq : mapping.size = size
  not_map_failed : mapping.addr.addr ≠ core.num.Usize.MAX
  range_fits : mapping.addr.addr.val + size.val ≤ Usize.max
  /-- Every supplied address passed the page-alignment check. A non-null fixed
      address is respected; `Some(null)` can enter the alignment-reservation path. -/
  fixed_address : match hint_addr with
    | some addr => addr.addr.val % pageSize.val = 0 ∧
        (addr.addr ≠ 0#usize → mapping.addr.addr = addr.addr)
    | none => True
  /-- Successful mappings are always page aligned, including fixed mappings. -/
  page_aligned : mapping.addr.addr.val % pageSize.val = 0
  /-- Zero requests default alignment. Every positive alignment is a power of
      two and is satisfied, including requests with a supplied address. -/
  requested_alignment : match align with
    | some a => 0 < a.val → a.val.isPowerOfTwo ∧ mapping.addr.addr.val % a.val = 0
    | none => True

/-- Successful results satisfy the mathematical mapping contract. Ordinary Rust
    errors are unconstrained; this does not assert that allocation succeeds.
    Aeneas panic/failure is still excluded by the enclosing function spec. -/
def MappingResultProperties (pageSize : Usize) (hint_addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64)
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  match result with
  | .Ok mapping => MappingProperties pageSize hint_addr size align mapping
  | .Err _ => True

/-- Wrappers may replace an absent alignment with zero without losing any of
    the success guarantees. -/
theorem MappingProperties.of_getD_zero {pageSize size : Usize}
    {hint_addr : Option (MutRawPtr U8)} {align : Option U64} {mapping : PlatformMemoryMapping}
    (h : MappingProperties pageSize hint_addr size (some (align.getD 0#u64)) mapping) :
    MappingProperties pageSize hint_addr size align mapping := by
  refine ⟨h.size_eq, h.not_map_failed, h.range_fits, h.fixed_address, h.page_aligned, ?_⟩
  cases align with
  | none => trivial
  | some a => exact h.requested_alignment

/-- Linux `PROT_*` bitmask corresponding to `Protection`. -/
def protectionFlags (prot : Protection) : I32 :=
  (if prot.read then PROT_READ else 0#i32) ||| (if prot.write then PROT_WRITE else 0#i32)

/-- Initial `MAP_SHARED` (and optional `MAP_POPULATE`) flags. -/
@[reducible]
def baseMmapFlags (populate : Bool) : I32 :=
  if populate then MAP_SHARED ||| MAP_POPULATE else MAP_SHARED

/-- Flags after applying `MAP_FIXED | MAP_NORESERVE` when an address is supplied. -/
@[reducible]
def addrMmapFlags (addr : Option (MutRawPtr U8)) (populate : Bool) : I32 :=
  match addr with
  | none => baseMmapFlags populate
  | some _ => baseMmapFlags populate ||| (MAP_FIXED ||| MAP_NORESERVE)

/-- Flags used for the anonymous alignment-reservation `mmap64` call
    (`MAP_PRIVATE | MAP_NORESERVE | MAP_ANONYMOUS`). -/
@[reducible]
private def reservationMmapFlags : I32 := (MAP_PRIVATE ||| MAP_NORESERVE) ||| MAP_ANONYMOUS

/-- Whether `fcntl(rawFd, F_GET_SEALS)` reports a non-negative seal mask with
    `F_SEAL_WRITE` set. -/
private def hasWriteSeal (rawFd : I32) : Bool :=
  let seals := _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS
  decide (seals ≥ 0#i32) && (seals &&& F_SEAL_WRITE != 0#i32)

/-- Final `mmap64` flags after adjusting for anonymous mapping or write-sealed fd. -/
private def targetMmapFlags (flags : I32) (rawFd : Option I32) : I32 :=
  match rawFd with
  | none => flags ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)
  | some fd =>
    if hasWriteSeal fd then (flags &&& ~~~MAP_SHARED) ||| MAP_PRIVATE else flags

/-- Normalize `align` by treating `Some(pagesize)` as `Some(0)`, matching
    `if align.unwrap_or(0) == pagesize() as u64 { Some(0) } else { align }`. -/
private def normalizeAlign (pageSize : Usize) (align : Option U64) : Option U64 :=
  if align.getD 0#u64 = UScalar.cast .U64 pageSize then some 0#u64 else align

/-- Round `origAddr` up to `align` using Rust's `wrapping_add(align - 1)` and `& !(align - 1)`. -/
@[reducible]
def alignVoidPtr (origAddr : VoidPtr) (align : U64) : VoidPtr :=
  let mask : U64 := UScalar.ofNatCore (align.val - 1) (by scalar_tac)
  let p1 : VoidPtr := { addr := core.num.Usize.wrapping_add origAddr.addr (UScalar.cast .Usize mask) }
  RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut (RawPtr.toUScalar .U64 p1 &&& ~~~mask)

/-- The trait object's `as_raw_descriptor` accessor returns a raw file descriptor without panicking. -/
def ValidDescriptor (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor) : Prop :=
  ∃ rawFd, descriptor.inst.as_raw_descriptor descriptor.value = ok rawFd

private theorem cast_addr {T T' : Type} {M M' : Mutability} (p : RawPtr T M) :
    (RawPtr.cast T' M' p).addr = p.addr := rfl

private theorem ofUScalar_addr_val {T : Type} {M : Mutability} (x : Usize) :
    (RawPtr.ofUScalar T M x).addr.val = x.val := by
  simp only [RawPtr.ofUScalar, UScalar.cast_val_eq]
  exact Nat.mod_eq_of_lt (by scalar_tac)

private def fdMmapOutcome (pageSize : Usize) (reqAddr : VoidPtr) (size : Usize)
    (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  match fd with
  | none =>
    ∃ addr,
      MmapCallSpec pageSize reqAddr size prot (targetMmapFlags flags none) (-1)#i32 0#i64 addr ∧
      if addr = mapFailedPtr then
        result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
      else
        result = .Ok { addr := RawPtr.cast Std.U8 .Mut addr, size := size }
  | some (descriptor, offset) =>
    if I64.max < offset.val then
      result = .Err .InvalidOffset
    else
      ∃ rawFd addr,
        descriptor.inst.as_raw_descriptor descriptor.value = ok rawFd ∧
        MmapCallSpec pageSize reqAddr size prot (targetMmapFlags flags (some rawFd))
          rawFd (UScalar.hcast .I64 offset) addr ∧
        if addr = mapFailedPtr then
          result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
        else
          result = .Ok { addr := RawPtr.cast Std.U8 .Mut addr, size := size }

private theorem usize_cast_u64_val (x : Usize) :
    (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem u64_cast_usize_val_of_le (x : U64) (h : x.val ≤ Usize.max) :
    (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

/-- The value of `size.checked_add(align as usize)` on a 64-bit host. -/
private theorem checked_add_cast_val [Platform64] {size s : Usize} {a : U64}
    (h : Usize.checked_add size (UScalar.cast .Usize a) = some s) :
    s.val = size.val + a.val := by
  have hcast := Platform64.u64_cast_usize_val a
  have hs := Usize.checked_add_bv_spec size (UScalar.cast .Usize a)
  simp only [h] at hs
  omega

private theorem option_some_or_none {α : Type} (o : Option α) : (∃ x, o = some x) ∨ o = none := by
  cases o <;> simp

theorem alignVoidPtr_addr_val (origAddr : VoidPtr) (align : U64)
    (size origSize : Usize) (ha : align.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align.val)
    (hfit : origAddr.addr.val + origSize.val ≤ Usize.max) :
    (alignVoidPtr origAddr align).addr.val = alignUp origAddr.addr.val align.val := by
  have hapos : 0 < align.val := Nat.pos_of_isPowerOfTwo ha
  let mask : U64 := UScalar.ofNatCore (align.val - 1) (by scalar_tac)
  have hmask : mask.val = align.val - 1 := rfl
  have hmask_le : mask.val ≤ Usize.max := by scalar_tac
  have hcast_mask : (UScalar.cast .Usize mask).val = align.val - 1 := by
    rw [u64_cast_usize_val_of_le mask hmask_le, hmask]
  let p1 : VoidPtr :=
    { addr := core.num.Usize.wrapping_add origAddr.addr (UScalar.cast .Usize mask) }
  have hp1 : p1.addr.val = origAddr.addr.val + (align.val - 1) := by
    change (core.num.Usize.wrapping_add origAddr.addr (UScalar.cast .Usize mask)).val = _
    rw [core.num.Usize.wrapping_add_val_eq, hcast_mask, UScalar.size_def]
    have hmax_def : Usize.max = 2 ^ UScalarTy.Usize.numBits - 1 := by
      rw [Usize.max_def, Usize.numBits_def]
    apply Nat.mod_eq_of_lt
    omega
  have htoU64 : (RawPtr.toUScalar .U64 p1).val = origAddr.addr.val + (align.val - 1) := by
    simp only [RawPtr.toUScalar, usize_cast_u64_val, hp1]
  have hmasked :
      (RawPtr.toUScalar .U64 p1 &&& ~~~mask).val = alignUp origAddr.addr.val align.val := by
    rw [mask_alignDown (RawPtr.toUScalar .U64 p1) align mask ha hmask, htoU64,
      round_up_eq origAddr.addr.val align.val hapos]
  have hup_le : alignUp origAddr.addr.val align.val ≤ origAddr.addr.val + (align.val - 1) := by
    rw [← round_up_eq origAddr.addr.val align.val hapos]
    exact alignDown_le _ _
  simp only [alignVoidPtr, RawPtr.ofUScalar]
  rw [u64_cast_usize_val_of_le]
  · exact hmasked
  · rw [hmasked]
    scalar_tac

theorem alignVoidPtr_bounds (origAddr : VoidPtr) (align : U64)
    (size origSize : Usize) (ha : align.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align.val)
    (hfit : origAddr.addr.val + origSize.val ≤ Usize.max) :
    origAddr.addr.val ≤ (alignVoidPtr origAddr align).addr.val ∧
    (alignVoidPtr origAddr align).addr.val + size.val ≤ origAddr.addr.val + origSize.val ∧
    (alignVoidPtr origAddr align).addr.val % align.val = 0 := by
  have hapos : 0 < align.val := Nat.pos_of_isPowerOfTwo ha
  have hval := alignVoidPtr_addr_val origAddr align size origSize ha horig hfit
  have hle := le_alignUp origAddr.addr.val align.val
  have hup_le : alignUp origAddr.addr.val align.val ≤ origAddr.addr.val + (align.val - 1) := by
    rw [← round_up_eq origAddr.addr.val align.val hapos]
    exact alignDown_le _ _
  have hmod := alignUp_mod origAddr.addr.val align.val hapos
  rw [hval]
  refine ⟨hle, by omega, hmod⟩

/-- The aligned mapping ends strictly before the reservation does, because
    rounding up moves the start by less than `align`. -/
theorem alignVoidPtr_end_lt (origAddr : VoidPtr) (align : U64)
    (size origSize : Usize) (ha : align.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align.val)
    (hfit : origAddr.addr.val + origSize.val ≤ Usize.max) :
    (alignVoidPtr origAddr align).addr.val + size.val < origAddr.addr.val + origSize.val := by
  have hapos : 0 < align.val := Nat.pos_of_isPowerOfTwo ha
  have hup_le : alignUp origAddr.addr.val align.val ≤ origAddr.addr.val + (align.val - 1) := by
    rw [← round_up_eq origAddr.addr.val align.val hapos]
    exact alignDown_le _ _
  rw [alignVoidPtr_addr_val origAddr align size origSize ha horig hfit]
  omega

private theorem targetMmapFlags_map_fixed_or (addr : Option (MutRawPtr U8)) (populate : Bool)
    (rawFd : Option I32) :
    targetMmapFlags (addrMmapFlags addr populate ||| MAP_FIXED) rawFd &&& MAP_FIXED ≠ 0#i32 := by
  cases addr <;> cases populate <;> cases rawFd with
  | none =>
    simp only [targetMmapFlags, addrMmapFlags, baseMmapFlags]
    decide
  | some fd =>
    by_cases h : hasWriteSeal fd <;>
      simp only [targetMmapFlags, addrMmapFlags, baseMmapFlags, h, ↓reduceIte] <;>
      decide

private theorem targetMmapFlags_map_fixed_some (reqAddr : MutRawPtr U8) (populate : Bool)
    (rawFd : Option I32) :
    targetMmapFlags (addrMmapFlags (some reqAddr) populate) rawFd &&& MAP_FIXED ≠ 0#i32 := by
  cases populate <;> cases rawFd with
  | none =>
    simp only [targetMmapFlags, addrMmapFlags, baseMmapFlags]
    decide
  | some fd =>
    by_cases h : hasWriteSeal fd <;>
      simp only [targetMmapFlags, addrMmapFlags, baseMmapFlags, h, ↓reduceIte] <;>
      decide

private theorem fdMmapOutcome_ok_spec {pageSize : Usize} {reqAddr : VoidPtr}
    {size : Usize} {prot flags : I32}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {mapping : PlatformMemoryMapping}
    (h : fdMmapOutcome pageSize reqAddr size prot flags fd (.Ok mapping)) :
    mapping.size = size ∧
    mapping.addr.addr ≠ core.num.Usize.MAX ∧
    mapping.addr.addr.val + size.val ≤ Usize.max ∧
    ((∀ rawFd, targetMmapFlags flags rawFd &&& MAP_FIXED ≠ 0#i32) →
      mapping.addr.addr = reqAddr.addr) ∧
    mapping.addr.addr.val % pageSize.val = 0 := by
  cases fd with
  | none =>
    obtain ⟨ret, hm, hs⟩ := h
    split at hs
    · simp at hs
    · rename_i hne
      simp only [core.result.Result.Ok.injEq] at hs
      subst hs
      obtain ⟨hfit, hfixed, hpage⟩ := hm.2 hne
      have hne' : ret.addr ≠ core.num.Usize.MAX := by
        intro heq
        apply hne
        cases ret
        simpa [mapFailedPtr] using heq
      exact ⟨rfl, hne', hfit, fun hf => congrArg RawPtr.addr (hfixed (hf none)), hpage.2⟩
  | some p =>
    rcases p with ⟨descriptor, offset⟩
    simp only [fdMmapOutcome] at h
    split at h
    · simp at h
    · obtain ⟨rawFd, ret, _, hm, hs⟩ := h
      split at hs
      · simp at hs
      · rename_i hne
        simp only [core.result.Result.Ok.injEq] at hs
        subst hs
        obtain ⟨hfit, hfixed, hpage⟩ := hm.2 hne
        have hne' : ret.addr ≠ core.num.Usize.MAX := by
          intro heq
          apply hne
          cases ret
          simpa [mapFailedPtr] using heq
        exact ⟨rfl, hne', hfit, fun hf => congrArg RawPtr.addr (hfixed (hf (some rawFd))), hpage.2⟩

/-- Recover the original positive alignment from the normalized request. -/
private theorem normalizeAlign_nonzero {pageSize : Usize} {align : Option U64} {a : U64}
    (hn : normalizeAlign pageSize align = some a) (ha : a ≠ 0#u64) :
    align = some a := by
  unfold normalizeAlign at hn
  split at hn
  · exact False.elim (ha (Option.some.inj hn).symm)
  · exact hn

/-- A request normalized to default alignment was absent, zero, or the page size. -/
private theorem default_requested_alignment {pageSize : Usize} {align : Option U64}
    {mapping : PlatformMemoryMapping}
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hn : normalizeAlign pageSize align = none ∨ normalizeAlign pageSize align = some 0#u64)
    (hpage : mapping.addr.addr.val % pageSize.val = 0) :
    match (generalizing := false) align with
    | some a => 0 < a.val → a.val.isPowerOfTwo ∧ mapping.addr.addr.val % a.val = 0
    | none => True := by
  cases halign : align with
  | none => trivial
  | some a =>
    intro hpos
    by_cases heq : a = UScalar.cast .U64 pageSize
    · rw [heq, usize_cast_u64_val]
      exact ⟨hPagePow, hpage⟩
    · have hz : a = 0#u64 := by simpa [normalizeAlign, halign, heq] using hn
      subst a
      simp at hpos

private theorem direct_none_properties {pageSize size : Usize} {align : Option U64}
    {prot : I32} {populate : Bool}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {result : core.result.Result PlatformMemoryMapping MmapError}
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hn : normalizeAlign pageSize align = none ∨ normalizeAlign pageSize align = some 0#u64)
    (h : fdMmapOutcome pageSize nullVoidPtr size prot (addrMmapFlags none populate)
      fd result) :
    MappingResultProperties pageSize none size align result := by
  cases result with
  | Err _ => trivial
  | Ok mapping =>
    obtain ⟨hsize, hne, hfit, _, hpage⟩ := fdMmapOutcome_ok_spec h
    exact ⟨hsize, hne, hfit, by simp, hpage,
      default_requested_alignment hPagePow hn hpage⟩

private theorem direct_fixed_properties {pageSize size : Usize} {align : Option U64}
    {reqAddr : MutRawPtr U8} {prot : I32} {populate : Bool}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {result : core.result.Result PlatformMemoryMapping MmapError}
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hn : normalizeAlign pageSize align = none ∨ normalizeAlign pageSize align = some 0#u64)
    (haligned : reqAddr.addr.val % pageSize.val = 0)
    (h : fdMmapOutcome pageSize (RawPtr.cast _ .Mut reqAddr) size prot
      (addrMmapFlags (some reqAddr) populate) fd result) :
    MappingResultProperties pageSize (some reqAddr) size align result := by
  cases result with
  | Err _ => trivial
  | Ok mapping =>
    obtain ⟨hsize, hne, hfit, hfixed, hpage⟩ := fdMmapOutcome_ok_spec h
    exact ⟨hsize, hne, hfit,
      ⟨haligned, fun _ => hfixed (targetMmapFlags_map_fixed_some reqAddr populate)⟩,
      hpage, default_requested_alignment hPagePow hn hpage⟩

private theorem aligned_properties {pageSize size origSize : Usize}
    {addr : Option (MutRawPtr U8)} {align : Option U64} {a : U64} {origAddr : VoidPtr}
    {prot : I32} {populate : Bool}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {result : core.result.Result PlatformMemoryMapping MmapError}
    (hn : normalizeAlign pageSize align = some a) (ha0 : a ≠ 0#u64)
    (hnull : ∀ p, addr = some p → p.addr = 0#usize)
    (hpow : a.val.isPowerOfTwo) (horig : origSize.val = size.val + a.val)
    (hfit_orig : origAddr.addr.val + origSize.val ≤ Usize.max)
    (h : fdMmapOutcome pageSize (alignVoidPtr origAddr a) size prot
      (addrMmapFlags addr populate ||| MAP_FIXED) fd result) :
    MappingResultProperties pageSize addr size align result := by
  cases result with
  | Err _ => trivial
  | Ok mapping =>
    obtain ⟨hsize, hne, hfit, hfixed, hpage⟩ := fdMmapOutcome_ok_spec h
    have heq := hfixed (targetMmapFlags_map_fixed_or addr populate)
    have hrequested := normalizeAlign_nonzero hn ha0
    subst align
    have hbounds := alignVoidPtr_bounds origAddr a size origSize hpow horig hfit_orig
    refine ⟨hsize, hne, hfit, ?_, hpage, ?_⟩
    · cases hp : addr with
      | none => trivial
      | some p =>
        exact ⟨by simp [hnull p hp], fun hne0 => False.elim (hne0 (hnull p hp))⟩
    · intro _
      exact ⟨hpow, by rw [heq]; exact hbounds.2.2⟩

@[step]
theorem protection_from_spec (p : Protection) :
    vm_memory.I32.Insts.CoreConvertFromProtection.from p ⦃ v => v = protectionFlags p ⦄ := by
  unfold vm_memory.I32.Insts.CoreConvertFromProtection.from protectionFlags
  cases p.read <;> cases p.write <;> simp <;> decide

private theorem baseMmapFlags_eval (populate : Bool) :
    (if populate = true then ok (MAP_SHARED ||| MAP_POPULATE) else ok MAP_SHARED : Result I32) =
      ok (baseMmapFlags populate) := by
  cases populate <;> rfl

private theorem normalizeAlign_eval (pageSize : Usize) (align : Option U64) :
    (if core.option.Option.unwrap_or align 0#u64 = UScalar.cast .U64 pageSize then
      ok (some 0#u64)
    else ok align : Result (Option U64)) = ok (normalizeAlign pageSize align) := by
  cases align with
  | none =>
    simp only [normalizeAlign, core.option.Option.unwrap_or, Option.getD_none]
    split <;> rfl
  | some a =>
    simp only [normalizeAlign, core.option.Option.unwrap_or, Option.getD_some]
    split <;> rfl

private theorem seal_flags_eval (f : I32) (rawFd : I32) :
    (if _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS ≥ 0#i32 then
      if (_root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS &&& F_SEAL_WRITE != 0#i32) = true then
        ok ((f &&& ~~~MAP_SHARED) ||| MAP_PRIVATE)
      else ok f
    else ok f : Result I32) = ok (targetMmapFlags f (some rawFd)) := by
  simp only [targetMmapFlags, hasWriteSeal, Bool.and_eq_true, decide_eq_true_eq]
  by_cases h1 : _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS ≥ 0#i32 <;>
    by_cases h2 : (_root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS &&& F_SEAL_WRITE != 0#i32) = true <;>
    simp [h1, h2]

private theorem i64_max_hcast_eq :
    IScalar.hcast .U64 core.num.I64.MAX = 9223372036854775807#u64 := rfl

private theorem offset_gt_i64_max_iff (offset : U64) :
    offset > IScalar.hcast .U64 core.num.I64.MAX ↔ I64.max < offset.val := by
  rw [i64_max_hcast_eq]
  scalar_tac

private theorem direct_fd_mmap_spec (pageSize : Usize) (reqAddr : VoidPtr) (size : Usize)
    (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize) :
    (match fd with
    | none => do
      let addr2 ← _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot
        (flags ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)) (-1)#i32 0#i64
      if addr2 = mapFailedPtr then
        let e ← _root_.base.errno.Error.last
        ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
      else
        ok (core.result.Result.Ok
          ({ addr := RawPtr.cast Std.U8 .Mut addr2, size } : PlatformMemoryMapping))
    | some p =>
      let (fd1, offset) := p
      if offset > IScalar.hcast .U64 core.num.I64.MAX then
        ok (core.result.Result.Err vm_memory.base.mmap.Error.InvalidOffset)
      else do
        let i4 ← fd1.inst.as_raw_descriptor fd1.value
        let flags2 ←
          if _root_.libc_1.unix.fcntl_status i4 F_GET_SEALS ≥ 0#i32 then
            if (_root_.libc_1.unix.fcntl_status i4 F_GET_SEALS &&& F_SEAL_WRITE != 0#i32) = true then
              ok ((flags &&& ~~~MAP_SHARED) ||| MAP_PRIVATE)
            else ok flags
          else ok flags
        let addr2 ← _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot flags2 i4
          (UScalar.hcast .I64 offset)
        if addr2 = mapFailedPtr then
          let e ← _root_.base.errno.Error.last
          ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
        else
          ok (core.result.Result.Ok
            ({ addr := RawPtr.cast Std.U8 .Mut addr2, size } : PlatformMemoryMapping))) ⦃ r =>
      fdMmapOutcome pageSize reqAddr size prot flags fd r ⦄ := by
  cases fd with
  | none =>
    obtain ⟨ret, hm⟩ := hMmap reqAddr size prot (targetMmapFlags flags none) (-1)#i32 0#i64
    have hmmap := hm.1
    simp only [targetMmapFlags] at hmmap
    by_cases hfail : ret = mapFailedPtr
    · simp only [hmmap, hfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
      exact ⟨mapFailedPtr, hfail ▸ hm, by simp⟩
    · simp only [hmmap, hfail, bind_ok, ↓reduceIte, WP.spec_ok]
      exact ⟨ret, hm, by simp [hfail]⟩
  | some p =>
    rcases p with ⟨fd1, offset⟩
    by_cases hoff : I64.max < offset.val
    · have hoff' : offset > IScalar.hcast .U64 core.num.I64.MAX :=
        (offset_gt_i64_max_iff offset).mpr hoff
      simp [hoff', fdMmapOutcome, hoff]
    · have hoff' : ¬offset > IScalar.hcast .U64 core.num.I64.MAX :=
        fun h => hoff ((offset_gt_i64_max_iff offset).mp h)
      obtain ⟨rawFd, hdesc⟩ := hFd fd1 offset rfl
      obtain ⟨ret, hm⟩ := hMmap reqAddr size prot
        (targetMmapFlags flags (some rawFd)) rawFd (UScalar.hcast .I64 offset)
      have hmmap := hm.1
      by_cases hfail : ret = mapFailedPtr
      · simp only [hoff', ↓reduceIte, hdesc, bind_ok, seal_flags_eval, hmmap, hfail,
          _root_.base.errno.Error.last, WP.spec_ok]
        simp only [fdMmapOutcome, hoff, ↓reduceIte]
        exact ⟨rawFd, mapFailedPtr, hdesc, hfail ▸ hm, by simp⟩
      · simp only [hoff', ↓reduceIte, hdesc, bind_ok, seal_flags_eval, hmmap, hfail, WP.spec_ok]
        simp only [fdMmapOutcome, hoff, ↓reduceIte]
        exact ⟨rawFd, ret, hdesc, hm, by simp [hfail]⟩

private theorem rawPtr_toUScalar_usize {T : Type} {M : Mutability} (p : RawPtr T M) :
    RawPtr.toUScalar .Usize p = p.addr := by
  apply UScalar.eq_of_val_eq
  simp [RawPtr.toUScalar]

/-! ### Ghost copy of the alignment path

With a requested alignment, `try_mmap_populate` reserves `size + align` bytes,
maps the aligned target over the reservation with `MAP_FIXED`, and unmaps the
unused prefix and suffix. `alignedMmapGhost` copies the translated code from
the reservation `mmap64` on, with `mmapGhost`, `mmapFixedGhost`, and
`munmapGhost` in place of the system calls, so that the ownership token flows
from call to call. `alignedMmap_erase` shows that dropping the token gives the
translated code, and `alignedMmapGhost_spec` shows that every call stays in
the owned reservation. -/

/-- Ghost copy of the trimming at the end of the alignment path. -/
def trimGhost (pageSize : Usize) (owned : Option Mapping) (origAddr addr3 : VoidPtr)
    (origSize size : Usize) :
    Result (core.result.Result PlatformMemoryMapping MmapError × Option Mapping) := do
  let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
  let owned1 ←
    if unmap_size > 0#usize then do
      let call ← munmapGhost pageSize owned origAddr unmap_size
      ok call.2
    else ok owned
  let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
  let i17 ← core.option.Option.unwrap (some origSize)
  let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + i17
  let unmap_size1 ← unmap_end1 - unmap_start1
  let owned2 ←
    if unmap_size1 > 0#usize then do
      let call ← munmapGhost pageSize owned1
        (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
      ok call.2
    else ok owned1
  ok (core.result.Result.Ok { addr := RawPtr.cast Std.U8 .Mut addr3, size }, owned2)

/-- Ghost copy of the alignment path of `try_mmap_populate`, from the
    reservation `mmap64` on. `flags` are the flags before `MAP_FIXED` is added. -/
def alignedMmapGhost (pageSize size origSize : Usize) (align : U64) (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)) :
    Result (core.result.Result PlatformMemoryMapping MmapError × Option Mapping) := do
  let reservation ← mmapGhost nullVoidPtr origSize prot
    (MAP_PRIVATE ||| MAP_NORESERVE ||| MAP_ANONYMOUS) (-1)#i32 0#i64
  let origAddr := reservation.1
  if origAddr = mapFailedPtr then do
    let e ← _root_.base.errno.Error.last
    ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e), reservation.2)
  else do
    let mask ← align - 1#u64
    let addr2 := RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut
      (RawPtr.toUScalar .U64
        ({ addr := core.num.Usize.wrapping_add origAddr.addr (UScalar.cast .Usize mask) } :
          VoidPtr) &&& ~~~mask)
    match fd with
    | none => do
      let fixed ← mmapFixedGhost reservation.2 addr2 size prot
        (flags ||| MAP_FIXED ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)) (-1)#i32 0#i64
      if fixed.1 = mapFailedPtr then do
        let e ← _root_.base.errno.Error.last
        ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e), fixed.2)
      else trimGhost pageSize fixed.2 origAddr fixed.1 origSize size
    | some (fd1, offset) =>
      if offset > IScalar.hcast .U64 core.num.I64.MAX then
        ok (core.result.Result.Err vm_memory.base.mmap.Error.InvalidOffset, reservation.2)
      else do
        let rawFd ← fd1.inst.as_raw_descriptor fd1.value
        let flags3 ←
          if _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS ≥ 0#i32 then
            if (_root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS &&& F_SEAL_WRITE != 0#i32) = true then
              ok ((flags ||| MAP_FIXED) &&& ~~~MAP_SHARED ||| MAP_PRIVATE)
            else ok (flags ||| MAP_FIXED)
          else ok (flags ||| MAP_FIXED)
        let fixed ← mmapFixedGhost reservation.2 addr2 size prot flags3 rawFd
          (UScalar.hcast .I64 offset)
        if fixed.1 = mapFailedPtr then do
          let e ← _root_.base.errno.Error.last
          ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e), fixed.2)
        else trimGhost pageSize fixed.2 origAddr fixed.1 origSize size

private theorem bind_ite {α β : Type} (p : Prop) [Decidable p]
    (yes no : Result α) (f : α → Result β) :
    Std.bind (if p then yes else no) f =
      if p then Std.bind yes f else Std.bind no f := by
  split <;> rfl

/-- Dropping the token from `alignedMmapGhost` gives the translated alignment
    path of `try_mmap_populate`, as it appears after evaluating the flag
    constants. -/
theorem alignedMmap_erase (pageSize size origSize : Usize) (align : U64) (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)) :
    (do
      let out ← alignedMmapGhost pageSize size origSize align prot flags fd
      ok out.1) =
    (do
      let orig_addr ←
        _root_.libc_1.unix.linux_like.mmap64 { addr := 0#usize } origSize prot
          (2#i32 ||| 16384#i32 ||| 32#i32) (-1)#i32 0#i64
      if orig_addr = { addr := core.num.Usize.MAX } then do
          let e ← _root_.base.errno.Error.last
          ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
        else do
          let mask ← align - 1#u64
          match fd with
            | none => do
              let addr3 ←
                _root_.libc_1.unix.linux_like.mmap64
                    (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut
                      (RawPtr.toUScalar .U64
                          ({ addr := core.num.Usize.wrapping_add orig_addr.addr (UScalar.cast .Usize mask) } : VoidPtr) &&&
                        ~~~mask))
                    size prot (flags ||| 16#i32 ||| (32#i32 ||| 16384#i32)) (-1)#i32 0#i64
              if addr3 = { addr := core.num.Usize.MAX } then do
                  let e ← _root_.base.errno.Error.last
                  ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
                else do
                  let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize orig_addr
                  if unmap_size > 0#usize then do
                      let _ ← _root_.libc_1.unix.munmap orig_addr unmap_size
                      ok ()
                    else ok ()
                  let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
                  let i17 ← core.option.Option.unwrap (some origSize)
                  let unmap_end1 ← RawPtr.toUScalar .Usize orig_addr + i17
                  let unmap_size1 ← unmap_end1 - unmap_start1
                  if unmap_size1 > 0#usize then do
                      let _ ←
                        _root_.libc_1.unix.munmap
                          (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
                      ok ()
                    else ok ()
                  ok (core.result.Result.Ok { addr := RawPtr.cast U8 .Mut addr3, size := size })
            | some p2 =>
              let (fd1, offset) := p2
              if offset > IScalar.hcast .U64 core.num.I64.MAX then
                ok (core.result.Result.Err vm_memory.base.mmap.Error.InvalidOffset)
              else do
                let i15 ← fd1.inst.as_raw_descriptor fd1.value
                let flags3 ←
                  if _root_.libc_1.unix.fcntl_status i15 1034#i32 ≥ 0#i32 then
                      if (_root_.libc_1.unix.fcntl_status i15 1034#i32 &&& 8#i32 != 0#i32) = true then
                        ok ((flags ||| 16#i32) &&& ~~~1#i32 ||| 2#i32)
                      else ok (flags ||| 16#i32)
                    else ok (flags ||| 16#i32)
                let addr3 ←
                  _root_.libc_1.unix.linux_like.mmap64
                      (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut
                        (RawPtr.toUScalar .U64
                            ({ addr := core.num.Usize.wrapping_add orig_addr.addr (UScalar.cast .Usize mask) } : VoidPtr) &&&
                          ~~~mask))
                      size prot flags3 i15 (UScalar.hcast .I64 offset)
                if addr3 = { addr := core.num.Usize.MAX } then do
                    let e ← _root_.base.errno.Error.last
                    ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
                  else do
                    let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize orig_addr
                    if unmap_size > 0#usize then do
                        let _ ← _root_.libc_1.unix.munmap orig_addr unmap_size
                        ok ()
                      else ok ()
                    let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
                    let i17 ← core.option.Option.unwrap (some origSize)
                    let unmap_end1 ← RawPtr.toUScalar .Usize orig_addr + i17
                    let unmap_size1 ← unmap_end1 - unmap_start1
                    if unmap_size1 > 0#usize then do
                        let _ ←
                          _root_.libc_1.unix.munmap
                            (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
                        ok ()
                      else ok ()
                    ok (core.result.Result.Ok { addr := RawPtr.cast U8 .Mut addr3, size := size })) := by
  unfold alignedMmapGhost trimGhost mmapGhost mmapFixedGhost munmapGhost
  cases fd with
  | none =>
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok, bind_ite]
  | some p =>
    rcases p with ⟨fd1, offset⟩
    dsimp only
    simp only [bind_tc_eq, Std.bind_assoc, bind_ok, bind_ite]
    rfl


private theorem spec_of_eq {α : Type} {m m' : Result α} {P : α → Prop} (h : m' = m)
    (hs : m' ⦃ x => P x ⦄) : m ⦃ x => P x ⦄ := h ▸ hs

/-- Starting from the owned reservation, the trimming returns the kept mapping
    `[addr3, addr3 + size)` and still owns a region of the reservation that
    contains it. Each `munmap` trims the token left by the previous call. -/
private theorem trimGhost_spec (pageSize : Usize) (origAddr addr3 : VoidPtr)
    (origSize size : Usize)
    (halign : addr3.addr.val % pageSize.val = 0)
    (hle : origAddr.addr.val ≤ addr3.addr.val)
    (hlt : addr3.addr.val + size.val < origAddr.addr.val + origSize.val)
    (hfit : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hMunmap : MunmapSpec) :
    trimGhost pageSize (some { addr := RawPtr.cast _ .Mut origAddr, size := origSize })
      origAddr addr3 origSize size ⦃ out =>
      out.1 = .Ok { addr := RawPtr.cast Std.U8 .Mut addr3, size } ∧
      ∃ tok, out.2 = some tok ∧
        Mapping.Contains { addr := RawPtr.cast _ .Mut origAddr, size := origSize } tok ∧
        Mapping.Contains tok { addr := RawPtr.cast _ .Mut addr3, size } ⦄ := by
  unfold trimGhost
  simp only [rawPtr_toUScalar_usize, core.option.Option.unwrap, ofOption, bind_ok]
  step as ⟨prefixLen, hpl⟩
  let reservation : Mapping := { addr := RawPtr.cast _ .Mut origAddr, size := origSize }
  -- After the prefix call, the token runs from at most `addr3` to the end of
  -- the reservation.
  have hprefix :
      (if prefixLen > 0#usize then do
        let call ← munmapGhost pageSize (some reservation) origAddr prefixLen
        ok call.2
      else ok (some reservation)) ⦃ owned1 =>
        ∃ m, owned1 = some m ∧ reservation.Contains m ∧
          m.addr.addr.val ≤ addr3.addr.val ∧
          m.addr.addr.val + m.size.val = origAddr.addr.val + origSize.val ⦄ := by
    by_cases hpos : prefixLen > 0#usize
    · obtain ⟨ret, hret⟩ := hMunmap origAddr prefixLen
      have hcan : reservation.CanTrim pageSize origAddr prefixLen :=
        ⟨by scalar_tac, by simp only [reservation]; omega,
          Or.inl ⟨rfl, by rw [show origAddr.addr.val + prefixLen.val = addr3.addr.val by omega]; exact halign⟩⟩
      have hend : origAddr.addr.val + prefixLen.val ≠
          reservation.addr.addr.val + reservation.size.val := by
        simp only [reservation, cast_addr]
        omega
      obtain ⟨ha, hs⟩ := Mapping.trim_prefix hend (by simp only [reservation]; omega) (by omega)
      simp only [hpos, ↓reduceIte, munmapGhost, hret, bind_ok, if_pos hcan, WP.spec_ok]
      refine ⟨_, rfl, ?_⟩
      split
      · refine ⟨hcan.contains_trim (by simp only [reservation, cast_addr]; omega), ?_, ?_⟩ <;>
          (simp only [ha, hs, reservation]; omega)
      · exact ⟨⟨le_rfl, le_rfl⟩, by simp only [reservation, cast_addr]; omega, rfl⟩
    · simp only [hpos, ↓reduceIte, WP.spec_ok]
      exact ⟨_, rfl, ⟨le_rfl, le_rfl⟩, by simp only [reservation, cast_addr]; omega, rfl⟩
  apply WP.spec_bind hprefix
  rintro owned1 ⟨m, rfl, hcontains, hstart, hend⟩
  step as ⟨suffixStart, hss⟩
  step as ⟨stop, hstop⟩
  step as ⟨suffixLen, hsl⟩
  have hkept : m.Contains { addr := RawPtr.cast _ .Mut addr3, size } := by
    simp only [Mapping.Contains, cast_addr]
    omega
  by_cases hpos : suffixLen > 0#usize
  · obtain ⟨ret, hret⟩ := hMunmap (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut suffixStart)
      suffixLen
    have hsuffix : (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut suffixStart).addr.val +
        suffixLen.val = m.addr.addr.val + m.size.val := by
      rw [ofUScalar_addr_val]
      omega
    have hcan : m.CanTrim pageSize (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut suffixStart)
        suffixLen := ⟨by scalar_tac, by omega, Or.inr hsuffix⟩
    obtain ⟨ha, hs⟩ := Mapping.trim_suffix hsuffix (by omega)
    simp only [hpos, ↓reduceIte, munmapGhost, hret, bind_ok, if_pos hcan, WP.spec_ok]
    refine ⟨trivial, _, rfl, ?_⟩
    split
    · refine ⟨hcontains.trans (hcan.contains_trim (by omega)), ?_⟩
      · simp only [Mapping.Contains, ha, hs, cast_addr]
        omega
    · exact ⟨hcontains, hkept⟩
  · simp only [hpos, ↓reduceIte, bind_ok, WP.spec_ok]
    exact ⟨trivial, m, rfl, hcontains, hkept⟩

/-- Outcome of the alignment path, with the token the ghost copy ends with.
    The reservation `mmap64` returns `origAddr`. If it succeeded, the aligned
    target is mapped as described by `fdMmapOutcome`. A successful result still
    owns a region of the reservation that contains the returned mapping. An
    error after the reservation still owns the whole reservation: the Rust code
    never unmaps it on these paths. -/
private def AlignedOutcome (pageSize size origSize : Usize) (align : U64) (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (result : core.result.Result PlatformMemoryMapping MmapError)
    (owned : Option Mapping) : Prop :=
  ∃ origAddr,
    MmapCallSpec pageSize nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64 origAddr ∧
    if origAddr = mapFailedPtr then
      result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
    else
      fdMmapOutcome pageSize (alignVoidPtr origAddr align) size prot (flags ||| MAP_FIXED) fd
        result ∧
      match result with
      | .Ok mapping => ∃ tok, owned = some tok ∧
          Mapping.Contains { addr := RawPtr.cast _ .Mut origAddr, size := origSize } tok ∧
          tok.Contains mapping
      | .Err _ => owned = some { addr := RawPtr.cast _ .Mut origAddr, size := origSize }

/-- The ghost copy of the alignment path keeps a valid token: the `MAP_FIXED`
    `mmap64` and both `munmap` calls stay inside the owned reservation, and a
    successful result is still owned. -/
private theorem alignedMmapGhost_spec (pageSize size origSize : Usize) (align : U64) (prot : I32)
    (addr : Option (MutRawPtr U8)) (populate : Bool)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (hpow : align.val.isPowerOfTwo) (horig : origSize.val = size.val + align.val)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize) (hMunmap : MunmapSpec) :
    alignedMmapGhost pageSize size origSize align prot (addrMmapFlags addr populate) fd ⦃ out =>
      AlignedOutcome pageSize size origSize align prot (addrMmapFlags addr populate) fd
        out.1 out.2 ⦄ := by
  unfold alignedMmapGhost mmapGhost
  obtain ⟨origAddr, hres⟩ := hMmap nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64
  have hmmap := hres.1
  simp only [reservationMmapFlags] at hmmap
  simp only [hmmap, bind_ok]
  by_cases hfail : origAddr = mapFailedPtr
  · simp only [hfail, ↓reduceIte, _root_.base.errno.Error.last, bind_ok, WP.spec_ok]
    exact ⟨origAddr, hres, by simp [hfail]⟩
  · obtain ⟨hfit_orig, _, _⟩ := hres.2 hfail
    simp only [hfail, ↓reduceIte]
    have hapos : 0 < align.val := Nat.pos_of_isPowerOfTwo hpow
    step as ⟨mask, hmask⟩
    have hexp : RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut
        (RawPtr.toUScalar .U64
          ({ addr := core.num.Usize.wrapping_add origAddr.addr (UScalar.cast .Usize mask) } :
            VoidPtr) &&& ~~~mask) = alignVoidPtr origAddr align := by
      rw [show mask = UScalar.ofNatCore (align.val - 1) (by scalar_tac) from
        UScalar.eq_of_val_eq hmask]
    simp only [hexp]
    have hbounds := alignVoidPtr_bounds origAddr align size origSize hpow horig hfit_orig
    have hend := alignVoidPtr_end_lt origAddr align size origSize hpow horig hfit_orig
    have htarget : Mapping.Contains { addr := RawPtr.cast _ .Mut origAddr, size := origSize }
        { addr := RawPtr.cast _ .Mut (alignVoidPtr origAddr align), size } := by
      simp only [Mapping.Contains, cast_addr]
      omega
    cases fd with
    | none =>
      obtain ⟨ret, hm⟩ := hMmap (alignVoidPtr origAddr align) size prot
        (targetMmapFlags (addrMmapFlags addr populate ||| MAP_FIXED) none) (-1)#i32 0#i64
      have hm1 := hm.1
      simp only [targetMmapFlags] at hm1
      simp only [mmapFixedGhost, hm1, bind_ok, if_pos htarget]
      by_cases hfail2 : ret = mapFailedPtr
      · simp only [hfail2, ↓reduceIte, _root_.base.errno.Error.last, bind_ok, WP.spec_ok]
        refine ⟨origAddr, hres, ?_⟩
        simp only [hfail, ↓reduceIte, fdMmapOutcome]
        exact ⟨⟨mapFailedPtr, hfail2 ▸ hm, by simp⟩, trivial⟩
      · obtain ⟨_, hfixed, _, halign⟩ := hm.2 hfail2
        have heq := hfixed (targetMmapFlags_map_fixed_or addr populate none)
        simp only [hfail2, ↓reduceIte]
        subst heq
        apply WP.spec_mono (trimGhost_spec pageSize origAddr (alignVoidPtr origAddr align)
          origSize size halign hbounds.1 hend hfit_orig hMunmap)
        rintro out ⟨hr, tok, hown, hres_tok, hkept⟩
        refine ⟨origAddr, hres, ?_⟩
        simp only [hfail, ↓reduceIte, fdMmapOutcome, hr]
        exact ⟨⟨alignVoidPtr origAddr align, hm, by simp [hfail2]⟩, tok, hown, hres_tok, hkept⟩
    | some p =>
      rcases p with ⟨fd1, offset⟩
      by_cases hoff : I64.max < offset.val
      · have hoff' : offset > IScalar.hcast .U64 core.num.I64.MAX :=
          (offset_gt_i64_max_iff offset).mpr hoff
        simp only [hoff', ↓reduceIte, WP.spec_ok]
        refine ⟨origAddr, hres, ?_⟩
        simp [hfail, fdMmapOutcome, hoff]
      · have hoff' : ¬offset > IScalar.hcast .U64 core.num.I64.MAX :=
          fun h => hoff ((offset_gt_i64_max_iff offset).mp h)
        obtain ⟨rawFd, hdesc⟩ := hFd fd1 offset rfl
        obtain ⟨ret, hm⟩ := hMmap (alignVoidPtr origAddr align) size prot
          (targetMmapFlags (addrMmapFlags addr populate ||| MAP_FIXED) (some rawFd))
          rawFd (UScalar.hcast .I64 offset)
        have hm1 := hm.1
        simp only [hoff', ↓reduceIte, hdesc, bind_ok, seal_flags_eval, mmapFixedGhost, hm1,
          if_pos htarget]
        by_cases hfail2 : ret = mapFailedPtr
        · simp only [hfail2, ↓reduceIte, _root_.base.errno.Error.last, bind_ok, WP.spec_ok]
          refine ⟨origAddr, hres, ?_⟩
          simp only [hfail, ↓reduceIte, fdMmapOutcome, hoff]
          exact ⟨⟨rawFd, mapFailedPtr, hdesc, hfail2 ▸ hm, by simp⟩, trivial⟩
        · obtain ⟨_, hfixed, _, halign⟩ := hm.2 hfail2
          have heq := hfixed (targetMmapFlags_map_fixed_or addr populate (some rawFd))
          simp only [hfail2, ↓reduceIte]
          subst heq
          apply WP.spec_mono (trimGhost_spec pageSize origAddr (alignVoidPtr origAddr align)
            origSize size halign hbounds.1 hend hfit_orig hMunmap)
          rintro out ⟨hr, tok, hown, hres_tok, hkept⟩
          refine ⟨origAddr, hres, ?_⟩
          simp only [hfail, ↓reduceIte, fdMmapOutcome, hoff, hr]
          exact ⟨⟨rawFd, alignVoidPtr origAddr align, hdesc, hm, by simp [hfail2]⟩,
            tok, hown, hres_tok, hkept⟩

private theorem aligned_outcome_properties {pageSize size origSize : Usize}
    {addr : Option (MutRawPtr U8)} {align : Option U64} {a : U64}
    {prot : I32} {populate : Bool}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {result : core.result.Result PlatformMemoryMapping MmapError} {owned : Option Mapping}
    (hn : normalizeAlign pageSize align = some a) (ha0 : a ≠ 0#u64)
    (hnull : ∀ p, addr = some p → p.addr = 0#usize)
    (hpow : a.val.isPowerOfTwo) (horig : origSize.val = size.val + a.val)
    (h : AlignedOutcome pageSize size origSize a prot (addrMmapFlags addr populate) fd
      result owned) :
    MappingResultProperties pageSize addr size align result := by
  obtain ⟨origAddr, hres, h⟩ := h
  by_cases hfail : origAddr = mapFailedPtr
  · simp only [hfail, ↓reduceIte] at h
    subst h
    trivial
  · simp only [hfail, ↓reduceIte] at h
    exact aligned_properties hn ha0 hnull hpow horig (hres.2 hfail).1 h.1

/-- Ownership on the alignment path: a successful result still owns a token
    that contains the returned mapping. So the `MAP_FIXED` `mmap64` and both
    `munmap` calls stayed inside the owned reservation and never unmapped the
    returned mapping. With `alignedMmap_erase`, this covers the alignment path
    of the translated `try_mmap_populate`. -/
theorem alignedMmapGhost_owns (pageSize size origSize : Usize) (align : U64) (prot : I32)
    (addr : Option (MutRawPtr U8)) (populate : Bool)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (hpow : align.val.isPowerOfTwo) (horig : origSize.val = size.val + align.val)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize) (hMunmap : MunmapSpec) :
    alignedMmapGhost pageSize size origSize align prot (addrMmapFlags addr populate) fd ⦃ out =>
      match out.1 with
      | .Ok mapping => ∃ tok, out.2 = some tok ∧ tok.Contains mapping
      | .Err _ => True ⦄ := by
  apply WP.spec_mono (alignedMmapGhost_spec pageSize size origSize align prot addr populate fd
    hpow horig hFd hMmap hMunmap)
  rintro ⟨result, owned⟩ ⟨origAddr, _, h⟩
  by_cases hfail : origAddr = mapFailedPtr
  · simp only [hfail, ↓reduceIte] at h
    subst h
    trivial
  · simp only [hfail, ↓reduceIte] at h
    obtain ⟨_, h⟩ := h
    cases result with
    | Ok mapping =>
      obtain ⟨tok, hown, _, hkept⟩ := h
      exact ⟨tok, hown, hkept⟩
    | Err _ => trivial

/-- The translated function directly satisfies the mathematical success contract.
    The alignment path is proved through its ghost copy (`alignedMmap_erase`,
    `alignedMmapGhost_owns`), and the ownership token is dropped here. The host
    page size is assumed to be a power of two: requests equal to it bypass the
    Rust power-of-two check. -/
@[step]
theorem try_mmap_populate_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      addr size align prot fd populate ⦃ result =>
      MappingResultProperties pageSize addr size align result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
  simp only [_root_.libc_1.unix.linux_like.MAP_SHARED, bind_ok, baseMmapFlags_eval]
  cases addr with
  | none =>
    simp only [lift, hPage, bind_ok, normalizeAlign_eval]
    cases hn : normalizeAlign pageSize align with
    | none =>
      apply WP.spec_mono (direct_fd_mmap_spec pageSize nullVoidPtr size prot
        (addrMmapFlags none populate) fd hFd hMmap)
      intro result hfd
      exact direct_none_properties hPagePow (Or.inl hn) hfd
    | some align2 =>
      dsimp only
      split
      · have hz : (0#64#uscalar : U64) = 0#u64 := rfl
        apply WP.spec_mono (direct_fd_mmap_spec pageSize nullVoidPtr size prot
          (addrMmapFlags none populate) fd hFd hMmap)
        intro result hfd
        exact direct_none_properties hPagePow (Or.inr (by simpa only [hz] using hn)) hfd
      · rename_i ha0
        have ha0' : align2 ≠ 0#u64 := ha0
        simp only [beq_self_eq_true, ↓reduceIte]
        step as ⟨b1, hb1⟩
        by_cases hpow : align2.val.isPowerOfTwo
        · have hb1_true : b1 = true := hb1.mpr hpow
          simp only [hb1_true, ↓reduceIte]
          obtain ⟨orig_size, hadd⟩ | hadd :=
            option_some_or_none (Usize.checked_add size (UScalar.cast .Usize align2))
          swap
          · simp only [hadd, core.option.Option.ok_or_none, bind_ok,
              core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
            step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
              _ (core.convert.FromSame _) _ _ rfl as ⟨result, hr⟩
            simp [hr, MappingResultProperties]
          simp only [hadd, core.option.Option.ok_or_some, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
          have horig := checked_add_cast_val hadd
          apply spec_of_eq (alignedMmap_erase pageSize size orig_size align2 prot _ fd)
          apply WP.spec_bind (alignedMmapGhost_spec pageSize size orig_size align2 prot none populate fd
            hpow horig hFd hMmap hMunmap)
          intro out hout
          simp only [WP.spec_ok]
          exact aligned_outcome_properties hn ha0' (by simp) hpow horig hout
        · have hb1_false : b1 = false := by
            cases b1 <;> simp_all
          simp only [hb1_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          trivial
  | some reqAddr =>
    have hpage_pos : 0 < pageSize.val := Nat.pos_of_isPowerOfTwo hPagePow
    dsimp only
    rw [rawPtr_toUScalar_usize reqAddr]
    simp only [lift, hPage, bind_ok]
    step as ⟨i2, hi2⟩
    by_cases hmod : reqAddr.addr.val % pageSize.val = 0
    · have hi2_eq : (i2 != 0#usize) = false := by
        rw [bne_eq_false_iff_eq]
        apply UScalar.eq_of_val_eq
        simpa [hi2] using hmod
      simp only [hi2_eq, Bool.false_eq_true, ↓reduceIte, bind_ok, normalizeAlign_eval]
      cases hn : normalizeAlign pageSize align with
      | none =>
        apply WP.spec_mono (direct_fd_mmap_spec pageSize (RawPtr.cast _ .Mut reqAddr) size prot
          (addrMmapFlags (some reqAddr) populate) fd hFd hMmap)
        intro result hfd
        exact direct_fixed_properties hPagePow (Or.inl hn) hmod hfd
      | some align2 =>
        dsimp only
        split
        · have hz : (0#64#uscalar : U64) = 0#u64 := rfl
          apply WP.spec_mono (direct_fd_mmap_spec pageSize (RawPtr.cast _ .Mut reqAddr) size prot
            (addrMmapFlags (some reqAddr) populate) fd hFd hMmap)
          intro result hfd
          exact direct_fixed_properties hPagePow (Or.inr (by simpa only [hz] using hn)) hmod hfd
        · rename_i ha0
          have ha0' : align2 ≠ 0#u64 := ha0
          by_cases hnull : reqAddr.addr = 0#usize
          · simp only [RawPtr.cast, hnull, beq_self_eq_true, ↓reduceIte]
            step as ⟨b1, hb1⟩
            by_cases hpow : align2.val.isPowerOfTwo
            · have hb1_true : b1 = true := hb1.mpr hpow
              simp only [hb1_true, ↓reduceIte]
              obtain ⟨orig_size, hadd⟩ | hadd :=
                option_some_or_none (Usize.checked_add size (UScalar.cast .Usize align2))
              swap
              · simp only [hadd, core.option.Option.ok_or_none, bind_ok,
                  core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
                step with
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
                  _ (core.convert.FromSame _) _ _ rfl as ⟨result, hr⟩
                simp [hr, MappingResultProperties]
              simp only [hadd, core.option.Option.ok_or_some, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
              have horig := checked_add_cast_val hadd
              apply spec_of_eq (alignedMmap_erase pageSize size orig_size align2 prot _ fd)
              apply WP.spec_bind (alignedMmapGhost_spec pageSize size orig_size align2 prot (some reqAddr) populate fd
                hpow horig hFd hMmap hMunmap)
              intro out hout
              simp only [WP.spec_ok]
              exact aligned_outcome_properties hn ha0' (by simpa using hnull) hpow horig hout
            · have hb1_false : b1 = false := by
                cases b1 <;> simp_all
              simp only [hb1_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
              trivial
          · simp only [RawPtr.cast, beq_iff_eq, hnull, ↓reduceIte, WP.spec_ok]
            trivial
    · have hi2_ne : (i2 != 0#usize) = true := by
        rw [bne_iff_ne]
        intro hzero
        apply hmod
        simpa [hi2] using congrArg UScalar.val hzero
      simp only [hi2_ne, ↓reduceIte, WP.spec_ok]
      trivial

/-- A nonzero alignment other than the page size must be a power of two.
    Otherwise the request is rejected before descriptor access or mapping calls.
    This theorem needs no syscall contracts or assumption on the page size. -/
theorem try_mmap_populate_invalid_alignment_spec (pageSize size : Usize)
    (align : U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (ha0 : align ≠ 0#u64) (hPageNe : align.val ≠ pageSize.val)
    (hpow : ¬align.val.isPowerOfTwo) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      none size (some align) prot fd populate ⦃ result =>
      result = .Err .InvalidAlignment ⦄ := by
  have hne : align ≠ UScalar.cast .U64 pageSize := by
    intro heq
    exact hPageNe (by rw [heq, usize_cast_u64_val])
  have hn : normalizeAlign pageSize (some align) = some align := by
    simp [normalizeAlign, hne]
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
  simp only [_root_.libc_1.unix.linux_like.MAP_SHARED, bind_ok, baseMmapFlags_eval,
    lift, hPage, normalizeAlign_eval, hn, ↓reduceIte, beq_self_eq_true]
  split
  · exact False.elim (ha0 rfl)
  · step as ⟨b, hb⟩
    have hb_false : b = false := by
      cases b <;> simp_all
    simp only [hb_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]

/-- A misaligned fixed address is rejected before descriptor access or mapping
    calls. This focused error theorem needs no syscall contracts. -/
theorem try_mmap_populate_not_page_aligned_spec (pageSize : Usize)
    (reqAddr : MutRawPtr U8) (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : 0 < pageSize.val)
    (hmod : reqAddr.addr.val % pageSize.val ≠ 0) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      (some reqAddr) size align prot fd populate ⦃ result =>
      result = .Err .NotPageAligned ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
  simp only [_root_.libc_1.unix.linux_like.MAP_SHARED, bind_ok, baseMmapFlags_eval]
  rw [rawPtr_toUScalar_usize reqAddr]
  simp only [lift, hPage, bind_ok]
  step as ⟨i2, hi2⟩
  have hi2_ne : (i2 != 0#usize) = true := by
    rw [bne_iff_ne]
    intro hzero
    apply hmod
    simpa [hi2] using congrArg UScalar.val hzero
  simp only [hi2_ne, ↓reduceIte, WP.spec_ok]

/-- Verify `MemoryMapping::try_mmap` as `try_mmap_populate` with `populate = false`. -/
@[step]
theorem try_mmap_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
      addr size align prot fd ⦃ result =>
      MappingResultProperties pageSize addr size align result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
  exact try_mmap_populate_spec pageSize addr size align prot fd false
    hPage hPagePow hFd hMmap hMunmap

/-- Verify `MemoryMapping::new_protection`: assuming `MmapSpec pageSize` and
    `MunmapSpec`, `new_protection` satisfies the mathematical success contract. -/
@[step]
theorem new_protection_spec (pageSize : Usize) (size : Usize) (align : Option U64)
    (protection : Protection)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
      size align protection ⦃ result =>
      MappingResultProperties pageSize none size align result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  exact try_mmap_spec pageSize none size align (protectionFlags protection) none
    hPage hPagePow (by simp) hMmap hMunmap

/-- Verify `MemoryMapping::from_fd_offset_protection_populate`: assuming
    `MmapSpec pageSize` and `MunmapSpec`, `from_fd_offset_protection_populate`
    satisfies the mathematical success contract. -/
@[step]
theorem from_fd_offset_protection_populate_spec (pageSize : Usize)
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hFd : ValidDescriptor descriptor)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
      descriptor size offset align protection populate ⦃ result =>
      MappingResultProperties pageSize none size (some align) result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  refine try_mmap_populate_spec pageSize none size (some align) (protectionFlags protection)
    (some (descriptor, offset)) populate hPage hPagePow ?_ hMmap hMunmap
  intro d off heq
  injection heq with heq
  injection heq with hd _
  subst hd
  exact hFd

end base.sys.linux.mmap.MemoryMapping
