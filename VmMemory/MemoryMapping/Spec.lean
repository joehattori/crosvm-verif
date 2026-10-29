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

/-- Reviewable properties of a successful returned mapping. These refer only
    to the request and returned value, not to flag updates or syscall order.

    This is a success-only abstraction of `TryMmapOutcome`, not an equivalent
    replacement for its error and syscall guarantees. In particular, it says
    nothing about memory contents, access permissions, ownership, or cleanup. -/
structure MappingProperties (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (mapping : PlatformMemoryMapping) : Prop where
  /-- The returned logical length is the requested length. -/
  size_eq : mapping.size = size
  /-- A successful result never contains the mmap failure sentinel. -/
  not_map_failed : mapping.addr.addr ≠ core.num.Usize.MAX
  /-- The end address is representable without wrapping. -/
  range_fits : mapping.addr.addr.val + size.val ≤ Usize.max
  /-- An explicitly requested non-null address is respected. `Some(null)`
      can enter the alignment-reservation path and is deliberately excluded. -/
  fixed_address : ∀ reqAddr, addr = some reqAddr → reqAddr.addr ≠ 0#usize →
    mapping.addr.addr = reqAddr.addr
  /-- With neither an address nor an alignment request, the result is page aligned.
      This field alone does not cover an explicit `Some(0)` alignment. -/
  default_alignment : addr = none → align = none →
    mapping.addr.addr.val % pageSize.val = 0
  /-- With no fixed address, every positive requested alignment is respected. -/
  requested_alignment : ∀ a, addr = none → align = some a → 0 < a.val →
    mapping.addr.addr.val % a.val = 0

/-- Linux `PROT_*` bitmask corresponding to `Protection`. -/
def protectionFlags (prot : Protection) : I32 :=
  (if prot.read then PROT_READ else 0#i32) ||| (if prot.write then PROT_WRITE else 0#i32)

/-- Initial `MAP_SHARED` (and optional `MAP_POPULATE`) flags. -/
@[reducible]
private def baseMmapFlags (populate : Bool) : I32 :=
  if populate then MAP_SHARED ||| MAP_POPULATE else MAP_SHARED

/-- Flags after applying `MAP_FIXED | MAP_NORESERVE` when an address is supplied. -/
@[reducible]
private def addrMmapFlags (addr : Option (MutRawPtr U8)) (populate : Bool) : I32 :=
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

/-- An unmap range `(unmapAddr, unmapLen)` is permitted during
    `try_mmap_populate` iff a non-zero power-of-two alignment distinct from
    `pageSize` was requested, the reservation `mmap64` call succeeded with
    `origAddr`, and `[unmapAddr, unmapAddr + unmapLen)` is a trimmed subrange
    of `[origAddr, origAddr + origSize)` strictly disjoint from the aligned
    target region `[alignVoidPtr origAddr a, alignVoidPtr origAddr a + size)`. -/
def TryMmapTrimAllowed (pageSize : Usize) (size : Usize) (align : Option U64) (prot : I32)
    (unmapAddr : VoidPtr) (unmapLen : Usize) : Prop :=
  let align := if align.getD 0#u64 = UScalar.cast .U64 pageSize then some 0#u64 else align
  ∃ a origSize origAddr,
    align = some a ∧ a ≠ 0#u64 ∧ a.val.isPowerOfTwo ∧
    Usize.checked_add size (UScalar.cast .Usize a) = some origSize ∧
    _root_.libc_1.unix.linux_like.mmap64 nullVoidPtr origSize prot
      ((MAP_PRIVATE ||| MAP_NORESERVE) ||| MAP_ANONYMOUS) (-1)#i32 0#i64 = ok origAddr ∧
    origAddr ≠ mapFailedPtr ∧
    IsTrimmedSubrange origAddr origSize (alignVoidPtr origAddr a) size unmapAddr unmapLen

theorem MunmapSpec.of_getD_zero {pageSize size : Usize} {align : Option U64} {prot : I32}
    (h : MunmapSpec (TryMmapTrimAllowed pageSize size align prot)) :
    MunmapSpec (TryMmapTrimAllowed pageSize size (some (align.getD 0#u64)) prot) := by
  intro addr len htrim
  apply h addr len
  cases align with
  | some x => exact htrim
  | none =>
    rcases htrim with ⟨a, _, _, hn, ha0, _⟩
    simp only [Option.getD_none, Option.getD_some, ite_self, Option.some.injEq] at hn
    exact False.elim (ha0 hn.symm)

/-- Without a requested alignment, no trimming `munmap` range is permitted, so
    the guarded specification holds vacuously. -/
theorem MunmapSpec.of_none (pageSize size : Usize) (prot : I32) :
    MunmapSpec (TryMmapTrimAllowed pageSize size none prot) := by
  rintro addr len ⟨a, _, _, hn, ha0, _⟩
  split at hn
  · exact False.elim (ha0 (Option.some.inj hn).symm)
  · simp at hn

private def trimMunmapOutcome (origAddr : Option VoidPtr) (origSize : Option Usize)
    (mappedAddr : VoidPtr) (size : Usize) : Prop :=
  match origAddr with
  | some rawOrigAddr =>
    let unmapStart := rawOrigAddr.addr.val
    let unmapEnd := mappedAddr.addr.val
    let unmapSize := unmapEnd - unmapStart
    (0 < unmapSize →
      ∃ (sz : Usize) (ret : I32),
        sz.val = unmapSize ∧
        MunmapCallSpec rawOrigAddr sz ret ∧
        ∀ rawOrigSize, origSize = some rawOrigSize →
          IsTrimmedSubrange rawOrigAddr rawOrigSize mappedAddr size rawOrigAddr sz) ∧
    let unmapStart1 := mappedAddr.addr.val + size.val
    ∃ rawOrigSize, origSize = some rawOrigSize ∧
      let unmapEnd1 := rawOrigAddr.addr.val + rawOrigSize.val
      let unmapSize1 := unmapEnd1 - unmapStart1
      (0 < unmapSize1 →
        ∃ (ptr : VoidPtr) (sz : Usize) (ret : I32),
          ptr.addr.val = unmapStart1 ∧
          sz.val = unmapSize1 ∧
          MunmapCallSpec ptr sz ret ∧
          IsTrimmedSubrange rawOrigAddr rawOrigSize mappedAddr size ptr sz)
  | none => True

private def fdMmapOutcome (pageSize : Usize) (reqAddr : VoidPtr) (size : Usize)
    (prot flags : I32)
    (origAddr : Option VoidPtr) (origSize : Option Usize)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  match fd with
  | none =>
    ∃ addr,
      MmapCallSpec pageSize reqAddr size prot (targetMmapFlags flags none) (-1)#i32 0#i64 addr ∧
      if addr = mapFailedPtr then
        result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
      else
        trimMunmapOutcome origAddr origSize addr size ∧
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
          trimMunmapOutcome origAddr origSize addr size ∧
          result = .Ok { addr := RawPtr.cast Std.U8 .Mut addr, size := size }

/-- Detailed outcome of `try_mmap_populate`, composed from address validation,
    alignment reservation, and `fdMmapOutcome` (offset validation, the final
    mapping, and permitted trim calls). Error precedence is preserved.

    For a small, implementation-independent success contract, see
    `MappingProperties` and `try_mmap_populate_success_spec` below. This detailed
    predicate constrains modeled syscall results, not the OS memory state. -/
def TryMmapOutcome (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  vm_memory.base.sys.unix.system_info.pagesize = ok pageSize ∧
  match addr with
  | some reqAddr =>
    0 < pageSize.val ∧
    if reqAddr.addr.val % pageSize.val ≠ 0 then
      result = .Err .NotPageAligned
    else
      let voidAddr : VoidPtr := RawPtr.cast vm_memory.core.ffi.c_void .Mut reqAddr
      let flags := addrMmapFlags (some reqAddr) populate
      match normalizeAlign pageSize align with
      | none =>
        fdMmapOutcome pageSize voidAddr size prot flags none none fd result
      | some a =>
        if a = 0#u64 then
          fdMmapOutcome pageSize voidAddr size prot flags none none fd result
        else if voidAddr.addr ≠ 0#usize ∨ ¬a.val.isPowerOfTwo ∨
            Usize.checked_add size (UScalar.cast .Usize a) = none then
          result = .Err .InvalidAlignment
        else
          ∃ (origSize : Usize) (origAddr : VoidPtr),
            Usize.checked_add size (UScalar.cast .Usize a) = some origSize ∧
            MmapCallSpec pageSize nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64 origAddr ∧
            if origAddr = mapFailedPtr then
              result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
            else
              fdMmapOutcome pageSize (alignVoidPtr origAddr a) size prot (flags ||| MAP_FIXED)
                (some origAddr) (some origSize) fd result
  | none =>
    let flags := addrMmapFlags none populate
    match normalizeAlign pageSize align with
    | none =>
      fdMmapOutcome pageSize nullVoidPtr size prot flags none none fd result
    | some a =>
      if a = 0#u64 then
        fdMmapOutcome pageSize nullVoidPtr size prot flags none none fd result
      else if ¬a.val.isPowerOfTwo ∨ Usize.checked_add size (UScalar.cast .Usize a) = none then
        result = .Err .InvalidAlignment
      else
        ∃ (origSize : Usize) (origAddr : VoidPtr),
          Usize.checked_add size (UScalar.cast .Usize a) = some origSize ∧
          MmapCallSpec pageSize nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64 origAddr ∧
          if origAddr = mapFailedPtr then
            result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
          else
            fdMmapOutcome pageSize (alignVoidPtr origAddr a) size prot (flags ||| MAP_FIXED)
              (some origAddr) (some origSize) fd result

/-- Outcome of `MemoryMapping::new_protection`. -/
abbrev NewProtectionOutcome (pageSize : Usize) (size : Usize) (align : Option U64)
    (protection : Protection)
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  TryMmapOutcome pageSize none size align (protectionFlags protection) none false result

/-- Outcome of `MemoryMapping::from_fd_offset_protection_populate`. -/
abbrev FromFdOutcome (pageSize : Usize)
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  TryMmapOutcome pageSize none size (some align) (protectionFlags protection)
    (some (descriptor, offset)) populate result

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
    {origAddr : Option VoidPtr} {origSize : Option Usize}
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {mapping : PlatformMemoryMapping}
    (h : fdMmapOutcome pageSize reqAddr size prot flags origAddr origSize fd (.Ok mapping)) :
    mapping.size = size ∧
    mapping.addr.addr ≠ core.num.Usize.MAX ∧
    mapping.addr.addr.val + size.val ≤ Usize.max ∧
    ((∀ rawFd, targetMmapFlags flags rawFd &&& MAP_FIXED ≠ 0#i32) →
      mapping.addr.addr = reqAddr.addr) ∧
    (reqAddr = nullVoidPtr → mapping.addr.addr.val % pageSize.val = 0) := by
  cases fd with
  | none =>
    obtain ⟨ret, hm, hs⟩ := h
    split at hs
    · simp at hs
    · rename_i hne
      obtain ⟨_, hs⟩ := hs
      simp only [core.result.Result.Ok.injEq] at hs
      subst hs
      obtain ⟨hfit, hfixed, hpage⟩ := hm.2 hne
      have hne' : ret.addr ≠ core.num.Usize.MAX := by
        intro heq
        apply hne
        cases ret
        simpa [mapFailedPtr] using heq
      exact ⟨rfl, hne', hfit, fun hf => congrArg RawPtr.addr (hfixed (hf none)), hpage⟩
  | some p =>
    rcases p with ⟨descriptor, offset⟩
    simp only [fdMmapOutcome] at h
    split at h
    · simp at h
    · obtain ⟨rawFd, ret, _, hm, hs⟩ := h
      split at hs
      · simp at hs
      · rename_i hne
        obtain ⟨_, hs⟩ := hs
        simp only [core.result.Result.Ok.injEq] at hs
        subst hs
        obtain ⟨hfit, hfixed, hpage⟩ := hm.2 hne
        have hne' : ret.addr ≠ core.num.Usize.MAX := by
          intro heq
          apply hne
          cases ret
          simpa [mapFailedPtr] using heq
        exact ⟨rfl, hne', hfit, fun hf => congrArg RawPtr.addr (hfixed (hf (some rawFd))), hpage⟩

/-- Properties guaranteed by `TryMmapOutcome` whenever a mapping succeeds with `.Ok mapping`. -/
theorem TryMmapOutcome.mapped_properties [Platform64] {pageSize : Usize}
    {addr : Option (MutRawPtr U8)} {size : Usize} {align : Option U64}
    {prot : I32} {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {populate : Bool} {mapping : PlatformMemoryMapping}
    (h : TryMmapOutcome pageSize addr size align prot fd populate (.Ok mapping)) :
    mapping.size = size ∧
    mapping.addr.addr ≠ core.num.Usize.MAX ∧
    mapping.addr.addr.val + size.val ≤ Usize.max ∧
    (∀ reqAddr, addr = some reqAddr → reqAddr.addr ≠ 0#usize → mapping.addr.addr = reqAddr.addr) ∧
    (addr = none → align = none → mapping.addr.addr.val % pageSize.val = 0) ∧
    (∀ a, addr = none → align = some a → 0 < a.val → mapping.addr.addr.val % a.val = 0) := by
  rcases h with ⟨_, hbody⟩
  cases addr with
  | some reqAddr =>
    rcases hbody with ⟨_, halign_page⟩
    split at halign_page
    · simp at halign_page
    · cases hn : normalizeAlign pageSize align with
      | none =>
        rw [hn] at halign_page
        obtain ⟨hsize, hne, hfit, hfixed, _⟩ := fdMmapOutcome_ok_spec halign_page
        have heq := hfixed (targetMmapFlags_map_fixed_some reqAddr populate)
        refine ⟨hsize, hne, hfit, ?_, by simp, by simp⟩
        intro r hr _
        injection hr with hr
        subst hr
        exact heq
      | some a =>
        rw [hn] at halign_page
        by_cases ha0 : a = 0#u64
        · simp only [ha0, ↓reduceIte] at halign_page
          obtain ⟨hsize, hne, hfit, hfixed, _⟩ := fdMmapOutcome_ok_spec halign_page
          have heq := hfixed (targetMmapFlags_map_fixed_some reqAddr populate)
          refine ⟨hsize, hne, hfit, ?_, by simp, by simp⟩
          intro r hr _
          injection hr with hr
          subst hr
          exact heq
        · simp only [ha0, ↓reduceIte] at halign_page
          split at halign_page
          · simp at halign_page
          · rename_i hcond
            push Not at hcond
            obtain ⟨hnull, _⟩ := hcond
            obtain ⟨_, origAddr, _, _, hfd⟩ := halign_page
            split at hfd
            · simp at hfd
            · obtain ⟨hsize, hne, hfit, _, _⟩ := fdMmapOutcome_ok_spec hfd
              refine ⟨hsize, hne, hfit, ?_, by simp, by simp⟩
              intro r hr hne0
              injection hr with hr
              subst hr
              exact False.elim (hne0 hnull)
  | none =>
    cases hn : normalizeAlign pageSize align with
    | none =>
      rw [hn] at hbody
      obtain ⟨hsize, hne, hfit, _, hpage⟩ := fdMmapOutcome_ok_spec hbody
      refine ⟨hsize, hne, hfit, by simp, fun _ _ => hpage rfl, ?_⟩
      intro a _ halign
      simp [normalizeAlign, halign] at hn
      split at hn <;> simp at hn
    | some a =>
      rw [hn] at hbody
      by_cases ha0 : a = 0#u64
      · simp only [ha0, ↓reduceIte] at hbody
        obtain ⟨hsize, hne, hfit, _, hpage⟩ := fdMmapOutcome_ok_spec hbody
        refine ⟨hsize, hne, hfit, by simp, fun _ => ?_, ?_⟩
        · intro halign
          exact hpage rfl
        · intro reqAlign _ halign hpos
          simp only [normalizeAlign, halign, Option.getD_some] at hn
          by_cases hcast : reqAlign = UScalar.cast .U64 pageSize
          · have hval : reqAlign.val = pageSize.val := by
              rw [hcast, usize_cast_u64_val]
            rw [hval]
            exact hpage rfl
          · simp only [hcast, ↓reduceIte, Option.some.injEq] at hn
            subst hn
            rw [ha0] at hpos
            simp at hpos
      · simp only [ha0, ↓reduceIte] at hbody
        split at hbody
        · simp at hbody
        · rename_i hcond
          push Not at hcond
          obtain ⟨hpow, _⟩ := hcond
          obtain ⟨origSize, origAddr, hadd, hres, hfd⟩ := hbody
          split at hfd
          · simp at hfd
          · rename_i hne_orig
            obtain ⟨hfit_orig, _, _⟩ := hres.2 hne_orig
            obtain ⟨hsize, hne, hfit, hfixed, _⟩ := fdMmapOutcome_ok_spec hfd
            have heq := hfixed (targetMmapFlags_map_fixed_or none populate)
            refine ⟨hsize, hne, hfit, by simp, ?_, ?_⟩
            · intro _ halign
              simp only [normalizeAlign, halign, Option.getD_none] at hn
              split at hn
              · injection hn with hn
                exact False.elim (ha0 hn.symm)
              · simp at hn
            · intro reqAlign _ halign _
              have horig := checked_add_cast_val hadd
              have hbounds := alignVoidPtr_bounds origAddr a size origSize hpow horig hfit_orig
              simp only [normalizeAlign, halign, Option.getD_some] at hn
              split at hn
              · injection hn with hn
                exact False.elim (ha0 hn.symm)
              · injection hn with hn
                subst hn
                rw [heq]
                exact hbounds.2.2

/-- The detailed outcome implies the reviewable success contract. The converse
    is not claimed: the detailed outcome also constrains errors and syscalls. -/
theorem TryMmapOutcome.mapping_properties [Platform64] {pageSize : Usize}
    {addr : Option (MutRawPtr U8)} {size : Usize} {align : Option U64}
    {prot : I32} {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {populate : Bool} {mapping : PlatformMemoryMapping}
    (h : TryMmapOutcome pageSize addr size align prot fd populate (.Ok mapping)) :
    MappingProperties pageSize addr size align mapping := by
  obtain ⟨hsize, hsentinel, hfit, hfixed, hpage, halign⟩ := h.mapped_properties
  exact ⟨hsize, hsentinel, hfit, hfixed, hpage, halign⟩

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
      fdMmapOutcome pageSize reqAddr size prot flags none none fd r ⦄ := by
  cases fd with
  | none =>
    obtain ⟨ret, hm⟩ := hMmap reqAddr size prot (targetMmapFlags flags none) (-1)#i32 0#i64
    have hmmap := hm.1
    simp only [targetMmapFlags] at hmmap
    by_cases hfail : ret = mapFailedPtr
    · simp only [hmmap, hfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
      exact ⟨mapFailedPtr, hfail ▸ hm, by simp⟩
    · simp only [hmmap, hfail, bind_ok, ↓reduceIte, WP.spec_ok]
      exact ⟨ret, hm, by simp [hfail, trimMunmapOutcome]⟩
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
        exact ⟨rawFd, ret, hdesc, hm, by simp [hfail, trimMunmapOutcome]⟩

private theorem rawPtr_toUScalar_usize {T : Type} {M : Mutability} (p : RawPtr T M) :
    RawPtr.toUScalar .Usize p = p.addr := by
  apply UScalar.eq_of_val_eq
  simp [RawPtr.toUScalar]

private theorem rawPtr_ofUScalar_usize_val (x : Usize) :
    (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut x).addr.val = x.val := by
  simp [RawPtr.ofUScalar]

private theorem unmap_tail_spec (origAddr addr3 : VoidPtr) (size origSize : Usize)
    (hle : origAddr.addr.val ≤ addr3.addr.val)
    (hfit1 : addr3.addr.val + size.val ≤ origAddr.addr.val + origSize.val)
    (hfit2 : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hMunmap : ∀ unmapAddr unmapLen,
      IsTrimmedSubrange origAddr origSize addr3 size unmapAddr unmapLen →
      ∃ ret, _root_.libc_1.unix.munmap unmapAddr unmapLen = ok ret) :
    (do
      let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
      let _ ←
        if unmap_size > 0#usize then do
          let _ ← _root_.libc_1.unix.munmap origAddr unmap_size
          ok ()
        else ok ()
      let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
      let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
      let unmap_size1 ← unmap_end1 - unmap_start1
      let _ ←
        if unmap_size1 > 0#usize then do
          let _ ← _root_.libc_1.unix.munmap
            (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
          ok ()
        else ok ()
      ok (core.result.Result.Ok
        ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping) :
        core.result.Result PlatformMemoryMapping MmapError)) ⦃ r =>
      trimMunmapOutcome (some origAddr) (some origSize) addr3 size ∧
      r = .Ok { addr := RawPtr.cast Std.U8 .Mut addr3, size := size } ⦄ := by
  simp only [rawPtr_toUScalar_usize]
  step as ⟨unmap_size, hunmap_size⟩
  have hprefix :
      (if unmap_size > 0#usize then do
        let _ ← _root_.libc_1.unix.munmap origAddr unmap_size
        ok ()
      else ok ()) ⦃ _ =>
        0 < addr3.addr.val - origAddr.addr.val →
          ∃ (sz : Usize) (ret : I32),
            sz.val = addr3.addr.val - origAddr.addr.val ∧
            MunmapCallSpec origAddr sz ret ∧
            IsTrimmedSubrange origAddr origSize addr3 size origAddr sz ⦄ := by
    by_cases hgt : unmap_size > 0#usize
    · have hpos : 0 < unmap_size.val := by scalar_tac
      have htrim : IsTrimmedSubrange origAddr origSize addr3 size origAddr unmap_size :=
        ⟨hpos, le_rfl, by omega, Or.inl (by omega)⟩
      obtain ⟨ret, hmunmap⟩ := hMunmap origAddr unmap_size htrim
      simp only [hgt, ↓reduceIte, hmunmap, bind_ok, WP.spec_ok]
      intro _
      exact ⟨unmap_size, ret, hunmap_size, ⟨hmunmap, hpos, by omega⟩, htrim⟩
    · simp only [hgt, ↓reduceIte, WP.spec_ok]
      intro hpos
      have : unmap_size > 0#usize := by scalar_tac
      exact False.elim (hgt this)
  step with hprefix as ⟨hp1⟩
  step as ⟨unmap_start1, hstart1⟩
  step as ⟨unmap_end1, hend1⟩
  step as ⟨unmap_size1, hunmap_size1⟩
  let p2 : VoidPtr := RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1
  have hp2 : p2.addr.val = unmap_start1.val := rawPtr_ofUScalar_usize_val unmap_start1
  have hsuffix :
      (if unmap_size1 > 0#usize then do
        let _ ← _root_.libc_1.unix.munmap p2 unmap_size1
        ok ()
      else ok ()) ⦃ _ =>
        0 < (origAddr.addr.val + origSize.val) - (addr3.addr.val + size.val) →
          ∃ (ptr : VoidPtr) (sz : Usize) (ret : I32),
            ptr.addr.val = addr3.addr.val + size.val ∧
            sz.val = (origAddr.addr.val + origSize.val) - (addr3.addr.val + size.val) ∧
            MunmapCallSpec ptr sz ret ∧
            IsTrimmedSubrange origAddr origSize addr3 size ptr sz ⦄ := by
    by_cases hgt1 : unmap_size1 > 0#usize
    · have hpos1 : 0 < unmap_size1.val := by scalar_tac
      have htrim1 : IsTrimmedSubrange origAddr origSize addr3 size p2 unmap_size1 :=
        ⟨hpos1, by omega, by omega, Or.inr (by omega)⟩
      obtain ⟨ret1, hmunmap1⟩ := hMunmap p2 unmap_size1 htrim1
      simp only [hgt1, ↓reduceIte, hmunmap1, bind_ok, WP.spec_ok]
      intro _
      exact ⟨p2, unmap_size1, ret1, by omega, by omega, ⟨hmunmap1, hpos1, by omega⟩, htrim1⟩
    · simp only [hgt1, ↓reduceIte, WP.spec_ok]
      intro hpos1
      have : unmap_size1 > 0#usize := by scalar_tac
      exact False.elim (hgt1 this)
  step with hsuffix as ⟨hp2_spec⟩
  refine ⟨fun hpos => ?_, origSize, rfl, hp2_spec⟩
  obtain ⟨sz, ret, hsz, hcall, htrim⟩ := hp1 hpos
  exact ⟨sz, ret, hsz, hcall, fun _ h => Option.some.inj h ▸ htrim⟩

private theorem aligned_fd_none_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (origAddr : VoidPtr) (align2 : U64) (size origSize : Usize)
    (prot : I32) (populate : Bool)
    (hpow : align2.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align2.val)
    (hfit_orig : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hMmap : MmapSpec pageSize)
    (hMunmap : ∀ unmapAddr unmapLen,
      IsTrimmedSubrange origAddr origSize (alignVoidPtr origAddr align2) size unmapAddr unmapLen →
      ∃ ret, _root_.libc_1.unix.munmap unmapAddr unmapLen = ok ret) :
    (let flags2 := addrMmapFlags addr populate ||| MAP_FIXED
    let addr2 := alignVoidPtr origAddr align2
    do
      let addr3 ← _root_.libc_1.unix.linux_like.mmap64 addr2 size prot
        (flags2 ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)) (-1)#i32 0#i64
      if addr3 = mapFailedPtr then
        let e ← _root_.base.errno.Error.last
        ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
      else do
        let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
        let _ ←
          if unmap_size > 0#usize then do
            let _ ← _root_.libc_1.unix.munmap origAddr unmap_size
            ok ()
          else ok ()
        let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
        let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
        let unmap_size1 ← unmap_end1 - unmap_start1
        let _ ←
          if unmap_size1 > 0#usize then do
            let _ ← _root_.libc_1.unix.munmap
              (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
            ok ()
          else ok ()
        ok (core.result.Result.Ok
          ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping))) ⦃ r =>
      fdMmapOutcome pageSize (alignVoidPtr origAddr align2) size prot
        (addrMmapFlags addr populate ||| MAP_FIXED) (some origAddr) (some origSize) none r ⦄ := by
  have hbounds := alignVoidPtr_bounds origAddr align2 size origSize hpow horig hfit_orig
  obtain ⟨ret, hm⟩ := hMmap (alignVoidPtr origAddr align2) size prot
    (targetMmapFlags (addrMmapFlags addr populate ||| MAP_FIXED) none) (-1)#i32 0#i64
  have hmmap := hm.1
  simp only [targetMmapFlags] at hmmap
  by_cases hfail : ret = mapFailedPtr
  · simp only [hmmap, hfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
    exact ⟨mapFailedPtr, hfail ▸ hm, by simp⟩
  · obtain ⟨_, hfixed, _⟩ := hm.2 hfail
    have heq := hfixed (targetMmapFlags_map_fixed_or addr populate none)
    simp only [hmmap, bind_ok, hfail, ↓reduceIte]
    subst heq
    apply WP.spec_mono (unmap_tail_spec origAddr (alignVoidPtr origAddr align2) size origSize
      hbounds.1 hbounds.2.1 hfit_orig hMunmap)
    intro r ⟨htrim, hr⟩
    exact ⟨alignVoidPtr origAddr align2, hm, by simp [hfail, htrim, hr]⟩

private theorem aligned_fd_some_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (origAddr : VoidPtr) (align2 : U64) (size origSize : Usize)
    (prot : I32) (populate : Bool)
    (fd1 : Dyn vm_memory.base.descriptor.AsRawDescriptor) (offset : U64)
    (hpow : align2.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align2.val)
    (hfit_orig : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hFd : ValidDescriptor fd1)
    (hMmap : MmapSpec pageSize)
    (hMunmap : ∀ unmapAddr unmapLen,
      IsTrimmedSubrange origAddr origSize (alignVoidPtr origAddr align2) size unmapAddr unmapLen →
      ∃ ret, _root_.libc_1.unix.munmap unmapAddr unmapLen = ok ret) :
    (let flags2 := addrMmapFlags addr populate ||| MAP_FIXED
    let addr2 := alignVoidPtr origAddr align2
    if offset > IScalar.hcast .U64 core.num.I64.MAX then
      ok (core.result.Result.Err vm_memory.base.mmap.Error.InvalidOffset)
    else do
      let i15 ← fd1.inst.as_raw_descriptor fd1.value
      let flags3 ←
        if _root_.libc_1.unix.fcntl_status i15 F_GET_SEALS ≥ 0#i32 then
          if (_root_.libc_1.unix.fcntl_status i15 F_GET_SEALS &&& F_SEAL_WRITE != 0#i32) = true then
            ok ((flags2 &&& ~~~MAP_SHARED) ||| MAP_PRIVATE)
          else ok flags2
        else ok flags2
      let addr3 ← _root_.libc_1.unix.linux_like.mmap64 addr2 size prot flags3 i15
        (UScalar.hcast .I64 offset)
      if addr3 = mapFailedPtr then
        let e ← _root_.base.errno.Error.last
        ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
      else do
        let unmap_size ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
        let _ ←
          if unmap_size > 0#usize then do
            let _ ← _root_.libc_1.unix.munmap origAddr unmap_size
            ok ()
          else ok ()
        let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
        let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
        let unmap_size1 ← unmap_end1 - unmap_start1
        let _ ←
          if unmap_size1 > 0#usize then do
            let _ ← _root_.libc_1.unix.munmap
              (RawPtr.ofUScalar vm_memory.core.ffi.c_void .Mut unmap_start1) unmap_size1
            ok ()
          else ok ()
        ok (core.result.Result.Ok
          ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping))) ⦃ r =>
      fdMmapOutcome pageSize (alignVoidPtr origAddr align2) size prot
        (addrMmapFlags addr populate ||| MAP_FIXED) (some origAddr) (some origSize)
        (some (fd1, offset)) r ⦄ := by
  have hbounds := alignVoidPtr_bounds origAddr align2 size origSize hpow horig hfit_orig
  by_cases hoff : I64.max < offset.val
  · have hoff' : offset > IScalar.hcast .U64 core.num.I64.MAX :=
      (offset_gt_i64_max_iff offset).mpr hoff
    simp [hoff', fdMmapOutcome, hoff]
  · have hoff' : ¬offset > IScalar.hcast .U64 core.num.I64.MAX :=
      fun h => hoff ((offset_gt_i64_max_iff offset).mp h)
    obtain ⟨rawFd, hdesc⟩ := hFd
    obtain ⟨ret, hm⟩ := hMmap (alignVoidPtr origAddr align2) size prot
      (targetMmapFlags (addrMmapFlags addr populate ||| MAP_FIXED) (some rawFd))
      rawFd (UScalar.hcast .I64 offset)
    have hmmap := hm.1
    by_cases hfail : ret = mapFailedPtr
    · simp only [hoff', ↓reduceIte, hdesc, bind_ok, seal_flags_eval, hmmap, hfail,
        _root_.base.errno.Error.last, WP.spec_ok]
      simp only [fdMmapOutcome, hoff, ↓reduceIte]
      exact ⟨rawFd, mapFailedPtr, hdesc, hfail ▸ hm, by simp⟩
    · obtain ⟨_, hfixed, _⟩ := hm.2 hfail
      have heq := hfixed (targetMmapFlags_map_fixed_or addr populate (some rawFd))
      simp only [hoff', ↓reduceIte, hdesc, bind_ok, seal_flags_eval, hmmap, hfail]
      subst heq
      apply WP.spec_mono (unmap_tail_spec origAddr (alignVoidPtr origAddr align2) size origSize
        hbounds.1 hbounds.2.1 hfit_orig hMunmap)
      intro r ⟨htrim, hr⟩
      simp only [fdMmapOutcome, hoff, ↓reduceIte]
      exact ⟨rawFd, alignVoidPtr origAddr align2, hdesc, hm, by simp [hfail, htrim, hr]⟩

/-- Verify `MemoryMapping::try_mmap_populate`: assuming `MmapSpec pageSize` and
    `MunmapSpec (TryMmapTrimAllowed pageSize size align prot)`,
    `try_mmap_populate` satisfies `TryMmapOutcome`. -/
@[step]
theorem try_mmap_populate_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : addr.isSome → 0 < pageSize.val)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec (TryMmapTrimAllowed pageSize size align prot)) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      addr size align prot fd populate ⦃ result =>
      TryMmapOutcome pageSize addr size align prot fd populate result ⦄ := by
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
      exact ⟨hPage, by simpa [TryMmapOutcome, hn] using hfd⟩
    | some align2 =>
      dsimp only
      split
      · have hz : (0#64#uscalar : U64) = 0#u64 := rfl
        apply WP.spec_mono (direct_fd_mmap_spec pageSize nullVoidPtr size prot
          (addrMmapFlags none populate) fd hFd hMmap)
        intro result hfd
        exact ⟨hPage, by simpa [TryMmapOutcome, hn, hz] using hfd⟩
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
            refine ⟨hPage, ?_⟩
            simp only [hn, ha0', hpow, hadd, not_true_eq_false, or_true, ↓reduceIte]
            exact hr
          simp only [hadd, core.option.Option.ok_or_some, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
          have horig := checked_add_cast_val hadd
          obtain ⟨origAddr, hres⟩ :=
            hMmap nullVoidPtr orig_size prot reservationMmapFlags (-1)#i32 0#i64
          have hmmap := hres.1
          simp only [reservationMmapFlags, nullVoidPtr] at hmmap
          by_cases hfail : origAddr = mapFailedPtr
          · have hmfail : origAddr = { addr := core.num.Usize.MAX } := hfail
            simp only [hmmap, hmfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
            refine ⟨hPage, ?_⟩
            simp only [hn, ha0', hpow, hadd, reduceCtorEq, not_true_eq_false, or_false, ↓reduceIte]
            exact ⟨orig_size, mapFailedPtr, rfl, hfail ▸ hres, by simp⟩
          · obtain ⟨hfit_orig, _, _⟩ := hres.2 hfail
            have hmne : origAddr ≠ { addr := core.num.Usize.MAX } := hfail
            have hMunmapLocal : ∀ unmapAddr unmapLen,
                IsTrimmedSubrange origAddr orig_size (alignVoidPtr origAddr align2) size
                  unmapAddr unmapLen →
                ∃ ret, _root_.libc_1.unix.munmap unmapAddr unmapLen = ok ret := by
              intro unmapAddr unmapLen htrim
              exact hMunmap unmapAddr unmapLen
                ⟨align2, orig_size, origAddr, hn, ha0', hpow, hadd, hres.1, hfail, htrim⟩
            simp only [hmmap, bind_ok, hmne, ↓reduceIte]
            have hapos : 0 < align2.val := Nat.pos_of_isPowerOfTwo hpow
            step as ⟨mask, hmask⟩
            have hmask_eq : mask = UScalar.ofNatCore (align2.val - 1) (by scalar_tac) := by
              apply UScalar.eq_of_val_eq
              exact hmask
            rw [hmask_eq]
            simp only [core.option.Option.unwrap, ofOption, bind_ok]
            cases fd with
            | none =>
              dsimp only
              apply WP.spec_mono (aligned_fd_none_spec pageSize none origAddr align2 size orig_size
                prot populate hpow horig hfit_orig hMmap hMunmapLocal)
              intro result hfd
              refine ⟨hPage, ?_⟩
              simp only [hn, ha0', hpow, hadd, reduceCtorEq, not_true_eq_false, or_false, ↓reduceIte]
              exact ⟨orig_size, origAddr, rfl, hres, by simp [hfail, hfd]⟩
            | some p2 =>
              rcases p2 with ⟨fd1, offset⟩
              dsimp only
              apply WP.spec_mono (aligned_fd_some_spec pageSize none origAddr align2 size orig_size
                prot populate fd1 offset hpow horig hfit_orig (hFd fd1 offset rfl) hMmap
                hMunmapLocal)
              intro result hfd
              refine ⟨hPage, ?_⟩
              simp only [hn, ha0', hpow, hadd, reduceCtorEq, not_true_eq_false, or_false, ↓reduceIte]
              exact ⟨orig_size, origAddr, rfl, hres, by simp [hfail, hfd]⟩
        · have hb1_false : b1 = false := by
            cases b1 <;> simp_all
          simp only [hb1_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨hPage, by simp [hn, ha0', hpow]⟩
  | some reqAddr =>
    have hpage_pos : 0 < pageSize.val := hPagePos rfl
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
        exact ⟨hPage, hpage_pos, by simpa [hmod, hn] using hfd⟩
      | some align2 =>
        dsimp only
        split
        · have hz : (0#64#uscalar : U64) = 0#u64 := rfl
          apply WP.spec_mono (direct_fd_mmap_spec pageSize (RawPtr.cast _ .Mut reqAddr) size prot
            (addrMmapFlags (some reqAddr) populate) fd hFd hMmap)
          intro result hfd
          exact ⟨hPage, hpage_pos, by simpa [hmod, hn, hz] using hfd⟩
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
                refine ⟨hPage, hpage_pos, ?_⟩
                simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                  hnull, hpow, hadd, or_true]
                exact hr
              simp only [hadd, core.option.Option.ok_or_some, bind_ok,
                core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
              have horig := checked_add_cast_val hadd
              obtain ⟨origAddr, hres⟩ :=
                hMmap nullVoidPtr orig_size prot reservationMmapFlags (-1)#i32 0#i64
              have hmmap := hres.1
              simp only [reservationMmapFlags, nullVoidPtr] at hmmap
              by_cases hfail : origAddr = mapFailedPtr
              · have hmfail : origAddr = { addr := core.num.Usize.MAX } := hfail
                simp only [hmmap, hmfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
                refine ⟨hPage, hpage_pos, ?_⟩
                simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                  hnull, hpow, hadd, reduceCtorEq, or_false]
                exact ⟨orig_size, mapFailedPtr, rfl, hfail ▸ hres, by simp⟩
              · obtain ⟨hfit_orig, _, _⟩ := hres.2 hfail
                have hmne : origAddr ≠ { addr := core.num.Usize.MAX } := hfail
                have hMunmapLocal : ∀ unmapAddr unmapLen,
                    IsTrimmedSubrange origAddr orig_size (alignVoidPtr origAddr align2) size
                      unmapAddr unmapLen →
                    ∃ ret, _root_.libc_1.unix.munmap unmapAddr unmapLen = ok ret := by
                  intro unmapAddr unmapLen htrim
                  exact hMunmap unmapAddr unmapLen
                    ⟨align2, orig_size, origAddr, hn, ha0', hpow, hadd, hres.1, hfail, htrim⟩
                simp only [hmmap, bind_ok, hmne, ↓reduceIte]
                have hapos : 0 < align2.val := Nat.pos_of_isPowerOfTwo hpow
                step as ⟨mask, hmask⟩
                have hmask_eq : mask = UScalar.ofNatCore (align2.val - 1) (by scalar_tac) := by
                  apply UScalar.eq_of_val_eq
                  exact hmask
                rw [hmask_eq]
                simp only [core.option.Option.unwrap, ofOption, bind_ok]
                cases fd with
                | none =>
                  dsimp only
                  apply WP.spec_mono (aligned_fd_none_spec pageSize (some reqAddr) origAddr align2
                    size orig_size prot populate hpow horig hfit_orig hMmap hMunmapLocal)
                  intro result hfd
                  refine ⟨hPage, hpage_pos, ?_⟩
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                    hnull, hpow, hadd, reduceCtorEq, or_false]
                  exact ⟨orig_size, origAddr, rfl, hres, by simp [hfail, hfd]⟩
                | some p3 =>
                  rcases p3 with ⟨fd1, offset⟩
                  dsimp only
                  apply WP.spec_mono (aligned_fd_some_spec pageSize (some reqAddr) origAddr align2
                    size orig_size prot populate fd1 offset hpow horig hfit_orig
                    (hFd fd1 offset rfl) hMmap hMunmapLocal)
                  intro result hfd
                  refine ⟨hPage, hpage_pos, ?_⟩
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                    hnull, hpow, hadd, reduceCtorEq, or_false]
                  exact ⟨orig_size, origAddr, rfl, hres, by simp [hfail, hfd]⟩
            · have hb1_false : b1 = false := by
                cases b1 <;> simp_all
              simp only [hb1_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
              exact ⟨hPage, hpage_pos, by simp [hn, ha0', hnull, hpow]⟩
          · simp only [RawPtr.cast, beq_iff_eq, hnull, ↓reduceIte, WP.spec_ok]
            exact ⟨hPage, hpage_pos, by simp [hmod, hn, ha0', RawPtr.cast, hnull]⟩
    · have hi2_ne : (i2 != 0#usize) = true := by
        rw [bne_iff_ne]
        intro hzero
        apply hmod
        simpa [hi2] using congrArg UScalar.val hzero
      simp only [hi2_ne, ↓reduceIte, WP.spec_ok]
      exact ⟨hPage, hpage_pos, by simp [hmod]⟩

/-- Verify `MemoryMapping::try_mmap` as `try_mmap_populate` with `populate = false`. -/
@[step]
theorem try_mmap_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : addr.isSome → 0 < pageSize.val)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec (TryMmapTrimAllowed pageSize size align prot)) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
      addr size align prot fd ⦃ result =>
      TryMmapOutcome pageSize addr size align prot fd false result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
  exact try_mmap_populate_spec pageSize addr size align prot fd false
    hPage hPagePos hFd hMmap hMunmap

/-- Verify `MemoryMapping::new_protection`: assuming `MmapSpec pageSize` and
    `MunmapSpec`, `new_protection` satisfies `NewProtectionOutcome`. -/
@[step]
theorem new_protection_spec (pageSize : Usize) (size : Usize) (align : Option U64)
    (protection : Protection)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec (TryMmapTrimAllowed pageSize size align (protectionFlags protection))) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
      size align protection ⦃ result =>
      NewProtectionOutcome pageSize size align protection result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  exact try_mmap_spec pageSize none size align (protectionFlags protection) none
    hPage (by simp) (by simp) hMmap hMunmap

/-- Verify `MemoryMapping::from_fd_offset_protection_populate`: assuming
    `MmapSpec pageSize` and `MunmapSpec`, `from_fd_offset_protection_populate`
    satisfies `FromFdOutcome`. -/
@[step]
theorem from_fd_offset_protection_populate_spec (pageSize : Usize)
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hFd : ValidDescriptor descriptor)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec
      (TryMmapTrimAllowed pageSize size (some align) (protectionFlags protection))) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
      descriptor size offset align protection populate ⦃ result =>
      FromFdOutcome pageSize descriptor size offset align protection populate result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  refine try_mmap_populate_spec pageSize none size (some align) (protectionFlags protection)
    (some (descriptor, offset)) populate hPage (by simp) ?_ hMmap hMunmap
  intro d off heq
  injection heq with heq
  injection heq with hd _
  subst hd
  exact hFd

/-- Direct connection from the translated function to `MappingProperties`, under
    exactly the assumptions of `try_mmap_populate_spec`. Errors are unconstrained
    here; use the detailed theorem when reasoning about error behavior. This is
    deliberately not registered with `step`, which should keep the stronger spec. -/
theorem try_mmap_populate_success_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : addr.isSome → 0 < pageSize.val)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec (TryMmapTrimAllowed pageSize size align prot)) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      addr size align prot fd populate ⦃ result =>
      match result with
      | .Ok mapping => MappingProperties pageSize addr size align mapping
      | .Err _ => True ⦄ := by
  apply WP.spec_mono (try_mmap_populate_spec pageSize addr size align prot fd populate
    hPage hPagePos hFd hMmap hMunmap)
  intro result houtcome
  cases result with
  | Ok mapping => exact houtcome.mapping_properties
  | Err _ => trivial

end base.sys.linux.mmap.MemoryMapping
