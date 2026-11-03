module
public import VmMemory.Funs
public import Syscalls.Memfd
@[expose] public section
open Aeneas Aeneas.Std Result
open Syscalls.Memfd

namespace vm_memory.base.shm.SharedMemory

/-! ### `PlatformSharedMemory::new` -/

/-- The `memfd_create` flags: close-on-exec and sealing, plus
    `MFD_NOEXEC_SEAL` when the host supports it. -/
def memfdFlags : U32 :=
  if _root_.base.sys.linux.shm.mfd_noexec_seal_supported then
    (MFD_CLOEXEC ||| MFD_ALLOW_SEALING) ||| MFD_NOEXEC_SEAL
  else MFD_CLOEXEC ||| MFD_ALLOW_SEALING

/-- Outcome of `PlatformSharedMemory::new`: create a memfd named `debugName`
    with `memfdFlags`, then set its size to `size as off64_t` with `ftruncate64`.
    A negative return from either call gives the last host error; otherwise
    the result owns the new descriptor and records `size`. -/
def PlatformNewOutcome (debugName : core.ffi.c_str.CStr) (size : U64)
    (result : core.result.Result SharedMemory _root_.base.errno.Error) : Prop :=
  let fd := _root_.base.sys.linux.shm.memfd_create_ret { addr := debugName.address } memfdFlags
  if fd < 0#i32 then result = .Err _root_.base.errno.Error.last_errno
  else if _root_.libc_1.unix.linux_like.ftruncate64_status fd (UScalar.hcast .I64 size) < 0#i32
  then result = .Err _root_.base.errno.Error.last_errno
  else result = .Ok { descriptor := { descriptor := fd }, size }

@[step]
theorem platform_new_spec (debugName : core.ffi.c_str.CStr) (size : U64) :
    Insts.BaseShmPlatformSharedMemory.new debugName size ⦃ result =>
      PlatformNewOutcome debugName size result ⦄ := by
  unfold Insts.BaseShmPlatformSharedMemory.new PlatformNewOutcome memfdFlags
  cases hs : _root_.base.sys.linux.shm.mfd_noexec_seal_supported <;>
    simp [hs, lift, RawPtr.cast, MFD_CLOEXEC, MFD_ALLOW_SEALING, MFD_NOEXEC_SEAL,
      vm_memory.base.descriptor.SafeDescriptor.Insts.BaseDescriptorAsRawDescriptor.as_raw_descriptor] <;>
    split_ifs <;> simp_all

/-! ### `SharedMemory::new` -/

/-- Outcome of `SharedMemory::new` for a debug name with bytes `bytes`: a name
    containing a NUL gives `EINVAL`; otherwise the result of
    `PlatformSharedMemory::new` for that C string. -/
def NewOutcome (bytes : List U8) (size : U64)
    (result : core.result.Result SharedMemory _root_.base.errno.Error) : Prop :=
  if 0#u8 ∈ bytes then result = .Err { errno := EINVAL }
  else PlatformNewOutcome { bytes } size result

@[step]
theorem new_spec {T : Type} (intoInst : core.convert.Into T (alloc.vec.Vec U8)) (debugName : T)
    (bytes : alloc.vec.Vec U8) (h : intoInst.into debugName = ok bytes) (size : U64) :
    new intoInst debugName size ⦃ result => NewOutcome bytes.val size result ⦄ := by
  unfold new NewOutcome
  by_cases hz : 0#u8 ∈ bytes.val
  · simp [_root_.alloc.ffi.c_str.CString.new, h, hz, core.result.Result.map_err,
      new.closure.Insts.CoreOpsFunctionFnOnceTupleNulErrorError.call_once,
      _root_.base.errno.Error.new, core.convert.TryInto.Blanket.try_into,
      _root_.core.convert.TryFromTUNever.Blanket.try_from,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [_root_.alloc.ffi.c_str.CString.new, h, hz, ↓reduceIte, bind_ok,
      core.result.Result.map_err_ok,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
      _root_.alloc.ffi.c_str.CString.Insts.CoreOpsDerefDerefCStr.deref]
    exact platform_new_spec _ _

/-- `size as off64_t` is non-negative only when `size` fits in `i64`. -/
private theorem hcast_i64_nonneg {x : U64} (h : 0 ≤ (UScalar.hcast .I64 x).val) :
    x.val ≤ I64.max := by
  rw [UScalar.hcast_val_eq] at h
  have hx : x.val < 2 ^ 64 := by
    have := x.hBounds
    simpa [UScalarTy.numBits] using this
  simp only [IScalarTy.numBits, Int.bmod_def] at h
  rw [I64.max_eq]
  split_ifs at h with hlt <;> omega

/-- A successful `PlatformSharedMemory::new` records the requested size. -/
theorem PlatformNewOutcome.ok_size {debugName : core.ffi.c_str.CStr} {size : U64}
    {shm : SharedMemory} (h : PlatformNewOutcome debugName size (.Ok shm)) :
    shm.size = size := by
  unfold PlatformNewOutcome at h
  dsimp only at h
  split_ifs at h
  simp_all

/-- Under `FtruncateSpec`, a successful `PlatformSharedMemory::new` has a size
    that fits in `off64_t`, so `ftruncate64` received the requested length. -/
theorem PlatformNewOutcome.size_le (hFt : FtruncateSpec) {debugName : core.ffi.c_str.CStr}
    {size : U64} {shm : SharedMemory} (h : PlatformNewOutcome debugName size (.Ok shm)) :
    size.val ≤ I64.max := by
  unfold PlatformNewOutcome at h
  dsimp only at h
  split_ifs at h with h1 h2
  apply hcast_i64_nonneg
  apply hFt
  simp only [IScalar.lt_equiv, not_lt] at h2
  simpa using h2

/-- A successful `SharedMemory::new` records the requested size. -/
theorem NewOutcome.ok_size {bytes : List U8} {size : U64} {shm : SharedMemory}
    (h : NewOutcome bytes size (.Ok shm)) : shm.size = size := by
  unfold NewOutcome at h
  split_ifs at h
  exact h.ok_size

/-- Under `FtruncateSpec`, a successful `SharedMemory::new` has a size that fits
    in `off64_t`. -/
theorem NewOutcome.size_le (hFt : FtruncateSpec) {bytes : List U8} {size : U64}
    {shm : SharedMemory} (h : NewOutcome bytes size (.Ok shm)) : size.val ≤ I64.max := by
  unfold NewOutcome at h
  split_ifs at h
  exact h.size_le hFt

/-! ### Seals -/

@[step]
theorem _root_.vm_memory.base.sys.linux.shm.MemfdSeals.new_spec :
    base.sys.linux.shm.MemfdSeals.new ⦃ seals => seals = (0#i32 : I32) ⦄ := by
  simp [base.sys.linux.shm.MemfdSeals.new]

@[step]
theorem _root_.vm_memory.base.sys.linux.shm.MemfdSeals.set_shrink_seal_spec
    (self : base.sys.linux.shm.MemfdSeals) :
    base.sys.linux.shm.MemfdSeals.set_shrink_seal self ⦃ seals =>
      seals = ((self : I32) ||| F_SEAL_SHRINK) ⦄ := by
  simp [base.sys.linux.shm.MemfdSeals.set_shrink_seal, lift]

@[step]
theorem _root_.vm_memory.base.sys.linux.shm.MemfdSeals.set_grow_seal_spec
    (self : base.sys.linux.shm.MemfdSeals) :
    base.sys.linux.shm.MemfdSeals.set_grow_seal self ⦃ seals =>
      seals = ((self : I32) ||| F_SEAL_GROW) ⦄ := by
  simp [base.sys.linux.shm.MemfdSeals.set_grow_seal, lift]

@[step]
theorem _root_.vm_memory.base.sys.linux.shm.MemfdSeals.set_seal_seal_spec
    (self : base.sys.linux.shm.MemfdSeals) :
    base.sys.linux.shm.MemfdSeals.set_seal_seal self ⦃ seals =>
      seals = ((self : I32) ||| F_SEAL_SEAL) ⦄ := by
  simp [base.sys.linux.shm.MemfdSeals.set_seal_seal, lift]

/-! ### `add_seals` -/

/-- Outcome of `SharedMemoryLinux::add_seals`: `fcntl(fd, F_ADD_SEALS, seals)`;
    a negative return gives the last host error. The shared memory value is
    unchanged. -/
def AddSealsOutcome (self : SharedMemory) (seals : base.sys.linux.shm.MemfdSeals)
    (result : core.result.Result Unit _root_.base.errno.Error × SharedMemory) : Prop :=
  result.2 = self ∧
  result.1 =
    if _root_.libc_1.unix.fcntl_status self.descriptor.descriptor F_ADD_SEALS seals < 0#i32
    then .Err _root_.base.errno.Error.last_errno
    else .Ok ()

@[step]
theorem add_seals_spec (self : SharedMemory) (seals : base.sys.linux.shm.MemfdSeals) :
    Insts.BaseSysLinuxShmSharedMemoryLinux.add_seals self seals ⦃ result =>
      AddSealsOutcome self seals result ⦄ := by
  unfold Insts.BaseSysLinuxShmSharedMemoryLinux.add_seals AddSealsOutcome
  simp only [vm_memory.base.descriptor.SafeDescriptor.Insts.BaseDescriptorAsRawDescriptor.as_raw_descriptor,
    _root_.libc_1.unix.linux_like.F_ADD_SEALS, _root_.libc_1.unix.fcntl, bind_ok]
  split_ifs <;> simp_all

end vm_memory.base.shm.SharedMemory
