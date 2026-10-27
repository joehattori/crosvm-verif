module
public import VmMemory.Funs
public import Syscalls.Mmap
public import Utils.Alignment
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

/-- Precondition that the alignment reservation size `size + align` fits in `usize`
    whenever a non-zero power-of-two alignment distinct from `pageSize` is requested. -/
def AlignSizeFits (pageSize : Usize) (size : Usize) (align : Option U64) : Prop :=
  let align := if align.getD 0#u64 = UScalar.cast .U64 pageSize then some 0#u64 else align
  ∀ a, align = some a → a ≠ 0#u64 → a.val.isPowerOfTwo →
    size.val + a.val ≤ Usize.max

theorem AlignSizeFits.of_getD_zero {pageSize size : Usize} {align : Option U64}
    (h : AlignSizeFits pageSize size align) :
    AlignSizeFits pageSize size (some (align.getD 0#u64)) := by
  cases align with
  | some x => exact h
  | none =>
    intro a hn ha0 _
    simp only [Option.getD_none, Option.getD_some, ite_self, Option.some.injEq] at hn
    exact False.elim (ha0 hn.symm)

open Classical in
/-- Outcome of `MemoryMapping::try_mmap_populate`, following its sequential
    `addr`, `align`, `fd`, and `flags` updates through the final `mmap64` call. -/
def TryMmapOutcome (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (result : core.result.Result PlatformMemoryMapping MmapError) : Prop :=
  let flags := MAP_SHARED
  let flags := if populate then flags ||| MAP_POPULATE else flags
  vm_memory.base.sys.unix.system_info.pagesize = ok pageSize ∧
  (addr.isSome → 0 < pageSize.val) ∧
  if ∃ reqAddr, addr = some reqAddr ∧ reqAddr.addr.val % pageSize.val ≠ 0 then
    result = .Err .NotPageAligned
  else
    let (addr, flags) : VoidPtr × I32 :=
      match addr with
      | some reqAddr =>
        let flags := flags ||| (MAP_FIXED ||| MAP_NORESERVE)
        (RawPtr.cast vm_memory.core.ffi.c_void .Mut reqAddr, flags)
      | none =>
        (nullVoidPtr, flags)
    let align := if align.getD 0#u64 = UScalar.cast .U64 pageSize then some 0#u64 else align
    if ∃ a, align = some a ∧ a ≠ 0#u64 ∧ (addr.addr ≠ 0#usize ∨ ¬a.val.isPowerOfTwo) then
      result = .Err .InvalidAlignment
    else
      ∃ (origAddr : Option VoidPtr),
        (match align with
        | none =>
          origAddr = none
        | some a =>
          if a = 0#u64 then
            origAddr = none
          else
            ∃ (origSize : Usize) (rawOrigAddr : VoidPtr),
              origSize.val = size.val + a.val ∧
              MmapCallSpec pageSize nullVoidPtr origSize prot
                ((MAP_PRIVATE ||| MAP_NORESERVE) ||| MAP_ANONYMOUS) (-1)#i32 0#i64 rawOrigAddr ∧
              origAddr = some rawOrigAddr) ∧
        if origAddr = some mapFailedPtr then
          result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
        else
          let (addr, flags) : VoidPtr × I32 :=
            match origAddr, align with
            | some rawOrigAddr, some a =>
              let flags := flags ||| MAP_FIXED
              let addr := alignVoidPtr rawOrigAddr a
              (addr, flags)
            | _, _ =>
              (addr, flags)
          if ∃ d offset, fd = some (d, offset) ∧ I64.max < offset.val then
            result = .Err .InvalidOffset
          else
            ∃ (rawFd : I32),
              (match fd with
              | some (descriptor, _) =>
                descriptor.inst.as_raw_descriptor descriptor.value = ok rawFd
              | none =>
                rawFd = (-1)#i32) ∧
              let (fd, offset, flags) : I32 × I64 × I32 :=
                match fd with
                | some (_, offset) =>
                  let seals := _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS
                  let flags :=
                    if decide (seals ≥ 0#i32) && (seals &&& F_SEAL_WRITE != 0#i32) then
                      (flags &&& ~~~MAP_SHARED) ||| MAP_PRIVATE
                    else
                      flags
                  (rawFd, UScalar.hcast .I64 offset, flags)
                | none =>
                  let flags := flags ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)
                  ((-1)#i32, 0#i64, flags)
              ∃ mappedAddr,
                MmapCallSpec pageSize addr size prot flags fd offset mappedAddr ∧
                if mappedAddr = mapFailedPtr then
                  result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
                else
                  result = .Ok { addr := RawPtr.cast Std.U8 .Mut mappedAddr, size := size }

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

private def tryMmapOutcomeCases (pageSize : Usize) (addr : Option (MutRawPtr U8))
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
        fdMmapOutcome pageSize voidAddr size prot flags fd result
      | some a =>
        if a = 0#u64 then
          fdMmapOutcome pageSize voidAddr size prot flags fd result
        else if voidAddr.addr ≠ 0#usize ∨ ¬a.val.isPowerOfTwo then
          result = .Err .InvalidAlignment
        else
          ∃ (origSize : Usize) (origAddr : VoidPtr),
            origSize.val = size.val + a.val ∧
            MmapCallSpec pageSize nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64 origAddr ∧
            if origAddr = mapFailedPtr then
              result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
            else
              fdMmapOutcome pageSize (alignVoidPtr origAddr a) size prot (flags ||| MAP_FIXED) fd result
  | none =>
    let flags := addrMmapFlags none populate
    match normalizeAlign pageSize align with
    | none =>
      fdMmapOutcome pageSize nullVoidPtr size prot flags fd result
    | some a =>
      if a = 0#u64 then
        fdMmapOutcome pageSize nullVoidPtr size prot flags fd result
      else if ¬a.val.isPowerOfTwo then
        result = .Err .InvalidAlignment
      else
        ∃ (origSize : Usize) (origAddr : VoidPtr),
          origSize.val = size.val + a.val ∧
          MmapCallSpec pageSize nullVoidPtr origSize prot reservationMmapFlags (-1)#i32 0#i64 origAddr ∧
          if origAddr = mapFailedPtr then
            result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
          else
            fdMmapOutcome pageSize (alignVoidPtr origAddr a) size prot (flags ||| MAP_FIXED) fd result

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
    {fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64)}
    {mapping : PlatformMemoryMapping}
    (h : fdMmapOutcome pageSize reqAddr size prot flags fd (.Ok mapping)) :
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
        simp only [core.result.Result.Ok.injEq] at hs
        subst hs
        obtain ⟨hfit, hfixed, hpage⟩ := hm.2 hne
        have hne' : ret.addr ≠ core.num.Usize.MAX := by
          intro heq
          apply hne
          cases ret
          simpa [mapFailedPtr] using heq
        exact ⟨rfl, hne', hfit, fun hf => congrArg RawPtr.addr (hfixed (hf (some rawFd))), hpage⟩

open Classical in
private theorem fd_stage_iff_fdMmapOutcome (pageSize : Usize) (addr : VoidPtr)
    (size : Usize) (prot flags : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (result : core.result.Result PlatformMemoryMapping MmapError) :
    (if ∃ d offset, fd = some (d, offset) ∧ I64.max < offset.val then
      result = .Err .InvalidOffset
    else
      ∃ (rawFd : I32),
        (match fd with
        | some (descriptor, _) =>
          descriptor.inst.as_raw_descriptor descriptor.value = ok rawFd
        | none =>
          rawFd = (-1)#i32) ∧
        let (fd, offset, flags) : I32 × I64 × I32 :=
          match fd with
          | some (_, offset) =>
            let seals := _root_.libc_1.unix.fcntl_status rawFd F_GET_SEALS
            let flags :=
              if decide (seals ≥ 0#i32) && (seals &&& F_SEAL_WRITE != 0#i32) then
                (flags &&& ~~~MAP_SHARED) ||| MAP_PRIVATE
              else
                flags
            (rawFd, UScalar.hcast .I64 offset, flags)
          | none =>
            let flags := flags ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)
            ((-1)#i32, 0#i64, flags)
        ∃ mappedAddr,
          MmapCallSpec pageSize addr size prot flags fd offset mappedAddr ∧
          if mappedAddr = mapFailedPtr then
            result = .Err (.SystemCallFailed _root_.base.errno.Error.last_errno)
          else
            result = .Ok { addr := RawPtr.cast Std.U8 .Mut mappedAddr, size := size }) ↔
      fdMmapOutcome pageSize addr size prot flags fd result := by
  cases fd with
  | none =>
    simp [fdMmapOutcome, targetMmapFlags]
  | some p =>
    rcases p with ⟨descriptor, offset⟩
    by_cases hoff : I64.max < offset.val
    · simp [fdMmapOutcome, hoff]
    · simp [fdMmapOutcome, targetMmapFlags, hasWriteSeal, hoff]

open Classical in
private theorem tryMmapOutcome_iff_cases (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (result : core.result.Result PlatformMemoryMapping MmapError) :
    TryMmapOutcome pageSize addr size align prot fd populate result ↔
      tryMmapOutcomeCases pageSize addr size align prot fd populate result := by
  have hn_def : (if align.getD 0#u64 = UScalar.cast .U64 pageSize then some 0#u64 else align) =
      normalizeAlign pageSize align := rfl
  unfold TryMmapOutcome tryMmapOutcomeCases
  cases addr with
  | none =>
    simp only [Option.isSome_none, Bool.false_eq_true, IsEmpty.forall_iff, true_and,
      reduceCtorEq, false_and, exists_false, ↓reduceIte, hn_def]
    refine and_congr_right fun _ => ?_
    cases hn : normalizeAlign pageSize align with
    | none =>
      simpa only [reduceCtorEq, false_and, exists_false, ↓reduceIte, exists_eq_left,
        addrMmapFlags, baseMmapFlags] using
        fd_stage_iff_fdMmapOutcome pageSize nullVoidPtr size prot
          (addrMmapFlags none populate) fd result
    | some a =>
      by_cases ha0 : a = 0#u64
      · subst ha0
        simpa only [Option.some.injEq, exists_eq_left', ne_eq, not_true_eq_false, false_and,
          ↓reduceIte, exists_eq_left, reduceCtorEq, addrMmapFlags, baseMmapFlags] using
          fd_stage_iff_fdMmapOutcome pageSize nullVoidPtr size prot
            (addrMmapFlags none populate) fd result
      · simp only [Option.some.injEq, exists_eq_left', ne_eq, not_true_eq_false, false_or,
          ha0, not_false_eq_true, true_and, ↓reduceIte]
        by_cases hpow : a.val.isPowerOfTwo
        · simp only [hpow, not_true_eq_false, ↓reduceIte]
          constructor
          · rintro ⟨origAddr, ⟨origSize, rawOrigAddr, horig, hmmap, rfl⟩, hrest⟩
            refine ⟨origSize, rawOrigAddr, horig, hmmap, ?_⟩
            by_cases hfail : rawOrigAddr = mapFailedPtr
            · simp_all
            · have hfd := (fd_stage_iff_fdMmapOutcome pageSize (alignVoidPtr rawOrigAddr a)
                size prot (addrMmapFlags none populate ||| MAP_FIXED) fd result).mp
              simpa only [Option.some.injEq, hfail, ↓reduceIte, addrMmapFlags, baseMmapFlags] using
                hfd (by simpa only [Option.some.injEq, hfail, ↓reduceIte,
                  addrMmapFlags, baseMmapFlags] using hrest)
          · rintro ⟨origSize, rawOrigAddr, horig, hmmap, hrest⟩
            refine ⟨some rawOrigAddr, ⟨origSize, rawOrigAddr, horig, hmmap, rfl⟩, ?_⟩
            by_cases hfail : rawOrigAddr = mapFailedPtr
            · simp_all
            · have hfd := (fd_stage_iff_fdMmapOutcome pageSize (alignVoidPtr rawOrigAddr a)
                size prot (addrMmapFlags none populate ||| MAP_FIXED) fd result).mpr
              simpa only [Option.some.injEq, hfail, ↓reduceIte, addrMmapFlags, baseMmapFlags] using
                hfd (by simpa only [Option.some.injEq, hfail, ↓reduceIte,
                  addrMmapFlags, baseMmapFlags] using hrest)
        · simp only [hpow, not_false_eq_true, ↓reduceIte]
  | some reqAddr =>
    simp only [Option.isSome_some, forall_const, Option.some.injEq, exists_eq_left', hn_def]
    refine and_congr_right fun _ => and_congr_right fun _ => ?_
    by_cases hmod : reqAddr.addr.val % pageSize.val ≠ 0
    · simp only [ne_eq] at hmod
      simp only [ne_eq, hmod, not_false_eq_true, ↓reduceIte]
    · simp only [hmod, ↓reduceIte]
      let voidAddr : VoidPtr := RawPtr.cast vm_memory.core.ffi.c_void .Mut reqAddr
      cases hn : normalizeAlign pageSize align with
      | none =>
        simpa only [reduceCtorEq, false_and, exists_false, ↓reduceIte, exists_eq_left,
          addrMmapFlags, baseMmapFlags] using
          fd_stage_iff_fdMmapOutcome pageSize voidAddr size prot
            (addrMmapFlags (some reqAddr) populate) fd result
      | some a =>
        by_cases ha0 : a = 0#u64
        · subst ha0
          simpa only [Option.some.injEq, exists_eq_left', ne_eq, not_true_eq_false, false_and,
            ↓reduceIte, exists_eq_left, reduceCtorEq, addrMmapFlags, baseMmapFlags] using
            fd_stage_iff_fdMmapOutcome pageSize voidAddr size prot
              (addrMmapFlags (some reqAddr) populate) fd result
        · simp only [Option.some.injEq, exists_eq_left', ne_eq, ha0, not_false_eq_true,
            true_and, ↓reduceIte]
          by_cases hbad : ¬(RawPtr.cast vm_memory.core.ffi.c_void .Mut reqAddr).addr = 0#usize ∨
              ¬a.val.isPowerOfTwo
          · simp only [hbad, ↓reduceIte]
          · simp only [hbad, ↓reduceIte]
            constructor
            · rintro ⟨origAddr, ⟨origSize, rawOrigAddr, horig, hmmap, rfl⟩, hrest⟩
              refine ⟨origSize, rawOrigAddr, horig, hmmap, ?_⟩
              by_cases hfail : rawOrigAddr = mapFailedPtr
              · simp_all
              · have hfd := (fd_stage_iff_fdMmapOutcome pageSize (alignVoidPtr rawOrigAddr a)
                  size prot (addrMmapFlags (some reqAddr) populate ||| MAP_FIXED) fd result).mp
                simpa only [Option.some.injEq, hfail, ↓reduceIte, addrMmapFlags, baseMmapFlags] using
                  hfd (by simpa only [Option.some.injEq, hfail, ↓reduceIte,
                    addrMmapFlags, baseMmapFlags] using hrest)
            · rintro ⟨origSize, rawOrigAddr, horig, hmmap, hrest⟩
              refine ⟨some rawOrigAddr, ⟨origSize, rawOrigAddr, horig, hmmap, rfl⟩, ?_⟩
              by_cases hfail : rawOrigAddr = mapFailedPtr
              · simp_all
              · have hfd := (fd_stage_iff_fdMmapOutcome pageSize (alignVoidPtr rawOrigAddr a)
                  size prot (addrMmapFlags (some reqAddr) populate ||| MAP_FIXED) fd result).mpr
                simpa only [Option.some.injEq, hfail, ↓reduceIte, addrMmapFlags, baseMmapFlags] using
                  hfd (by simpa only [Option.some.injEq, hfail, ↓reduceIte,
                    addrMmapFlags, baseMmapFlags] using hrest)

/-- Properties guaranteed by `TryMmapOutcome` whenever a mapping succeeds with `.Ok mapping`. -/
theorem TryMmapOutcome.mapped_properties {pageSize : Usize}
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
  rw [tryMmapOutcome_iff_cases] at h
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
        · rename_i hpow
          rw [Classical.not_not] at hpow
          obtain ⟨origSize, origAddr, horig, hres, hfd⟩ := hbody
          split at hfd
          · simp at hfd
          · rename_i hne_orig
            obtain ⟨hfit_orig, _, _⟩ := hres.2 hne_orig
            obtain ⟨hsize, hne, hfit, hfixed, _⟩ := fdMmapOutcome_ok_spec hfd
            have heq := hfixed (targetMmapFlags_map_fixed_or none populate)
            have hbounds := alignVoidPtr_bounds origAddr a size origSize hpow horig hfit_orig
            refine ⟨hsize, hne, hfit, by simp, ?_, ?_⟩
            · intro _ halign
              simp only [normalizeAlign, halign, Option.getD_none] at hn
              split at hn
              · injection hn with hn
                exact False.elim (ha0 hn.symm)
              · simp at hn
            · intro reqAlign _ halign _
              simp only [normalizeAlign, halign, Option.getD_some] at hn
              split at hn
              · injection hn with hn
                exact False.elim (ha0 hn.symm)
              · injection hn with hn
                subst hn
                rw [heq]
                exact hbounds.2.2

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

private theorem unmap_tail_spec (origAddr addr3 : VoidPtr) (size origSize : Usize)
    (hle : origAddr.addr.val ≤ addr3.addr.val)
    (hfit1 : addr3.addr.val + size.val ≤ origAddr.addr.val + origSize.val)
    (hfit2 : origAddr.addr.val + origSize.val ≤ Usize.max) :
    (do
      let _ ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
      let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
      let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
      let _ ← unmap_end1 - unmap_start1
      ok (core.result.Result.Ok
        ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping) :
        core.result.Result PlatformMemoryMapping MmapError)) ⦃ r =>
      r = .Ok { addr := RawPtr.cast Std.U8 .Mut addr3, size := size } ⦄ := by
  simp only [rawPtr_toUScalar_usize]
  step as ⟨unmap_size, _⟩
  step as ⟨unmap_start1, hstart1⟩
  step as ⟨unmap_end1, hend1⟩
  step as ⟨unmap_size1, _⟩

private theorem aligned_fd_none_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (origAddr : VoidPtr) (align2 : U64) (size origSize : Usize)
    (prot : I32) (populate : Bool)
    (hpow : align2.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align2.val)
    (hfit_orig : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hMmap : MmapSpec pageSize) :
    (let flags2 := addrMmapFlags addr populate ||| MAP_FIXED
    let addr2 := alignVoidPtr origAddr align2
    do
      let addr3 ← _root_.libc_1.unix.linux_like.mmap64 addr2 size prot
        (flags2 ||| (MAP_ANONYMOUS ||| MAP_NORESERVE)) (-1)#i32 0#i64
      if addr3 = mapFailedPtr then
        let e ← _root_.base.errno.Error.last
        ok (core.result.Result.Err (vm_memory.base.mmap.Error.SystemCallFailed e))
      else do
        let _ ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
        let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
        let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
        let _ ← unmap_end1 - unmap_start1
        ok (core.result.Result.Ok
          ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping))) ⦃ r =>
      fdMmapOutcome pageSize (alignVoidPtr origAddr align2) size prot
        (addrMmapFlags addr populate ||| MAP_FIXED) none r ⦄ := by
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
      hbounds.1 hbounds.2.1 hfit_orig)
    intro r hr
    exact ⟨alignVoidPtr origAddr align2, hm, by simp [hfail, hr]⟩

private theorem aligned_fd_some_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (origAddr : VoidPtr) (align2 : U64) (size origSize : Usize)
    (prot : I32) (populate : Bool)
    (fd1 : Dyn vm_memory.base.descriptor.AsRawDescriptor) (offset : U64)
    (hpow : align2.val.isPowerOfTwo)
    (horig : origSize.val = size.val + align2.val)
    (hfit_orig : origAddr.addr.val + origSize.val ≤ Usize.max)
    (hFd : ValidDescriptor fd1)
    (hMmap : MmapSpec pageSize) :
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
        let _ ← RawPtr.toUScalar .Usize addr3 - RawPtr.toUScalar .Usize origAddr
        let unmap_start1 ← RawPtr.toUScalar .Usize addr3 + size
        let unmap_end1 ← RawPtr.toUScalar .Usize origAddr + origSize
        let _ ← unmap_end1 - unmap_start1
        ok (core.result.Result.Ok
          ({ addr := RawPtr.cast Std.U8 .Mut addr3, size } : PlatformMemoryMapping))) ⦃ r =>
      fdMmapOutcome pageSize (alignVoidPtr origAddr align2) size prot
        (addrMmapFlags addr populate ||| MAP_FIXED) (some (fd1, offset)) r ⦄ := by
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
        hbounds.1 hbounds.2.1 hfit_orig)
      intro r hr
      simp only [fdMmapOutcome, hoff, ↓reduceIte]
      exact ⟨rawFd, alignVoidPtr origAddr align2, hdesc, hm, by simp [hfail, hr]⟩

/-- Verify `MemoryMapping::try_mmap_populate`: assuming `MmapSpec pageSize`,
    `try_mmap_populate` satisfies `TryMmapOutcome`. -/
@[step]
theorem try_mmap_populate_spec (pageSize : Usize) (addr : Option (MutRawPtr U8))
    (size : Usize) (align : Option U64) (prot : I32)
    (fd : Option (Dyn vm_memory.base.descriptor.AsRawDescriptor × U64))
    (populate : Bool)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : addr.isSome → 0 < pageSize.val)
    (hAlign : AlignSizeFits pageSize size align)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap_populate
      addr size align prot fd populate ⦃ result =>
      TryMmapOutcome pageSize addr size align prot fd populate result ⦄ := by
  simp only [tryMmapOutcome_iff_cases]
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
      exact ⟨hPage, by simpa [tryMmapOutcomeCases, hn] using hfd⟩
    | some align2 =>
      dsimp only
      split
      · have hz : (0#64#uscalar : U64) = 0#u64 := rfl
        apply WP.spec_mono (direct_fd_mmap_spec pageSize nullVoidPtr size prot
          (addrMmapFlags none populate) fd hFd hMmap)
        intro result hfd
        exact ⟨hPage, by simpa [tryMmapOutcomeCases, hn, hz] using hfd⟩
      · rename_i ha0
        have ha0' : align2 ≠ 0#u64 := ha0
        simp only [beq_self_eq_true, ↓reduceIte]
        step as ⟨b1, hb1⟩
        by_cases hpow : align2.val.isPowerOfTwo
        · have hb1_true : b1 = true := hb1.mpr hpow
          have hsize_align : size.val + align2.val ≤ Usize.max := hAlign align2 hn ha0' hpow
          simp only [hb1_true, ↓reduceIte]
          have hcast_align : (UScalar.cast .Usize align2).val = align2.val :=
            u64_cast_usize_val_of_le align2 (by scalar_tac)
          step as ⟨orig_size, horig_size⟩
          have horig : orig_size.val = size.val + align2.val := by omega
          obtain ⟨origAddr, hres⟩ :=
            hMmap nullVoidPtr orig_size prot reservationMmapFlags (-1)#i32 0#i64
          have hmmap := hres.1
          simp only [reservationMmapFlags, nullVoidPtr] at hmmap
          by_cases hfail : origAddr = mapFailedPtr
          · have hmfail : origAddr = { addr := core.num.Usize.MAX } := hfail
            simp only [hmmap, hmfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
            refine ⟨hPage, ?_⟩
            simp only [hn, ha0', hpow, not_true_eq_false, ↓reduceIte]
            exact ⟨orig_size, mapFailedPtr, horig, hfail ▸ hres, by simp⟩
          · obtain ⟨hfit_orig, _, _⟩ := hres.2 hfail
            have hmne : origAddr ≠ { addr := core.num.Usize.MAX } := hfail
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
                prot populate hpow horig hfit_orig hMmap)
              intro result hfd
              refine ⟨hPage, ?_⟩
              simp only [hn, ha0', hpow, not_true_eq_false, ↓reduceIte]
              exact ⟨orig_size, origAddr, horig, hres, by simp [hfail, hfd]⟩
            | some p2 =>
              rcases p2 with ⟨fd1, offset⟩
              dsimp only
              apply WP.spec_mono (aligned_fd_some_spec pageSize none origAddr align2 size orig_size
                prot populate fd1 offset hpow horig hfit_orig (hFd fd1 offset rfl) hMmap)
              intro result hfd
              refine ⟨hPage, ?_⟩
              simp only [hn, ha0', hpow, not_true_eq_false, ↓reduceIte]
              exact ⟨orig_size, origAddr, horig, hres, by simp [hfail, hfd]⟩
        · have hb1_false : b1 = false := by
            cases b1 <;> simp_all
          simp only [hb1_false, Bool.false_eq_true, ↓reduceIte, WP.spec_ok]
          exact ⟨hPage, by simp [hn, ha0', hpow]⟩
  | some reqAddr =>
    have hpage_pos : 0 < pageSize.val := hPagePos rfl
    dsimp only
    rw [rawPtr_toUScalar_usize reqAddr]
    simp only [lift, hPage, bind_ok, ite_self]
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
              have hsize_align : size.val + align2.val ≤ Usize.max := hAlign align2 hn ha0' hpow
              simp only [hb1_true, ↓reduceIte]
              have hcast_align : (UScalar.cast .Usize align2).val = align2.val :=
                u64_cast_usize_val_of_le align2 (by scalar_tac)
              step as ⟨orig_size, horig_size⟩
              have horig : orig_size.val = size.val + align2.val := by omega
              obtain ⟨origAddr, hres⟩ :=
                hMmap nullVoidPtr orig_size prot reservationMmapFlags (-1)#i32 0#i64
              have hmmap := hres.1
              simp only [reservationMmapFlags, nullVoidPtr] at hmmap
              by_cases hfail : origAddr = mapFailedPtr
              · have hmfail : origAddr = { addr := core.num.Usize.MAX } := hfail
                simp only [hmmap, hmfail, _root_.base.errno.Error.last, bind_ok, ↓reduceIte, WP.spec_ok]
                refine ⟨hPage, hpage_pos, ?_⟩
                simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                  hnull, false_or, hpow]
                exact ⟨orig_size, mapFailedPtr, horig, hfail ▸ hres, by simp⟩
              · obtain ⟨hfit_orig, _, _⟩ := hres.2 hfail
                have hmne : origAddr ≠ { addr := core.num.Usize.MAX } := hfail
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
                    size orig_size prot populate hpow horig hfit_orig hMmap)
                  intro result hfd
                  refine ⟨hPage, hpage_pos, ?_⟩
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                    hnull, false_or, hpow]
                  exact ⟨orig_size, origAddr, horig, hres, by simp [hfail, hfd]⟩
                | some p3 =>
                  rcases p3 with ⟨fd1, offset⟩
                  dsimp only
                  apply WP.spec_mono (aligned_fd_some_spec pageSize (some reqAddr) origAddr align2
                    size orig_size prot populate fd1 offset hpow horig hfit_orig
                    (hFd fd1 offset rfl) hMmap)
                  intro result hfd
                  refine ⟨hPage, hpage_pos, ?_⟩
                  simp only [ne_eq, not_true_eq_false, ↓reduceIte, hn, ha0', RawPtr.cast,
                    hnull, false_or, hpow]
                  exact ⟨orig_size, origAddr, horig, hres, by simp [hfail, hfd]⟩
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
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePos : addr.isSome → 0 < pageSize.val)
    (hAlign : AlignSizeFits pageSize size align)
    (hFd : ∀ d offset, fd = some (d, offset) → ValidDescriptor d)
    (hMmap : MmapSpec pageSize) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
      addr size align prot fd ⦃ result =>
      TryMmapOutcome pageSize addr size align prot fd false result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.try_mmap
  exact try_mmap_populate_spec pageSize addr size align prot fd false
    hPage hPagePos hAlign hFd hMmap

/-- Verify `MemoryMapping::new_protection`: assuming `MmapSpec pageSize`,
    `new_protection` satisfies `NewProtectionOutcome`. -/
@[step]
theorem new_protection_spec (pageSize : Usize) (size : Usize) (align : Option U64)
    (protection : Protection)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hAlign : AlignSizeFits pageSize size align)
    (hMmap : MmapSpec pageSize) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
      size align protection ⦃ result =>
      NewProtectionOutcome pageSize size align protection result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.new_protection
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  exact try_mmap_spec pageSize none size align (protectionFlags protection) none
    hPage (by simp) hAlign (by simp) hMmap

/-- Verify `MemoryMapping::from_fd_offset_protection_populate`: assuming
    `MmapSpec pageSize`, `from_fd_offset_protection_populate` satisfies
    `FromFdOutcome`. -/
@[step]
theorem from_fd_offset_protection_populate_spec (pageSize : Usize)
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hAlign : AlignSizeFits pageSize size (some align))
    (hFd : ValidDescriptor descriptor)
    (hMmap : MmapSpec pageSize) :
    vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
      descriptor size offset align protection populate ⦃ result =>
      FromFdOutcome pageSize descriptor size offset align protection populate result ⦄ := by
  unfold vm_memory.base.sys.linux.mmap.MemoryMapping.from_fd_offset_protection_populate
    core.convert.IntoFrom.into
  step as ⟨protFlags, hprot⟩
  subst hprot
  refine try_mmap_populate_spec pageSize none size (some align) (protectionFlags protection)
    (some (descriptor, offset)) populate hPage (by simp) hAlign ?_ hMmap
  intro d off heq
  injection heq with heq
  injection heq with hd _
  subst hd
  exact hFd

end base.sys.linux.mmap.MemoryMapping
