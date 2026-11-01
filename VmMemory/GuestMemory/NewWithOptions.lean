module
public import VmMemory.GuestMemory.Spec
public import VmMemory.SharedMemory.Spec
public import VmMemory.MemoryMappingBuilder.Spec
public import Utils.Platform
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address
open Syscalls.Memfd

namespace vm_memory.guest_memory.GuestMemory

/-! ### `finalize_shm` -/

/-- The seals `finalize_shm` adds: no shrinking, no growing, and no further
    seals. -/
def finalizeSeals : I32 := F_SEAL_SHRINK ||| F_SEAL_GROW ||| F_SEAL_SEAL

/-- Outcome of `finalize_shm`: add `finalizeSeals` to the shared memory; an
    error becomes `MemoryAddSealsFailed`. -/
def FinalizeShmOutcome (shm : base.shm.SharedMemory)
    (result : core.result.Result Unit vm_memory.guest_memory.Error × base.shm.SharedMemory) :
    Prop :=
  ∃ added, shm.AddSealsOutcome finalizeSeals added ∧ result.2 = added.2 ∧
    result.1 = match added.1 with
      | .Ok () => .Ok ()
      | .Err e => .Err (.MemoryAddSealsFailed e)

@[step]
theorem finalize_shm_spec (shm : base.shm.SharedMemory) :
    sys.linux.finalize_shm shm ⦃ result => FinalizeShmOutcome shm result ⦄ := by
  unfold sys.linux.finalize_shm
  have hseals : ((0#i32 ||| F_SEAL_SHRINK) ||| F_SEAL_GROW) ||| F_SEAL_SEAL = finalizeSeals := by
    rfl
  simp only [base.sys.linux.shm.MemfdSeals.new, base.sys.linux.shm.MemfdSeals.set_shrink_seal,
    base.sys.linux.shm.MemfdSeals.set_grow_seal, base.sys.linux.shm.MemfdSeals.set_seal_seal,
    _root_.libc_1.unix.linux_like.F_SEAL_SHRINK, _root_.libc_1.unix.linux_like.F_SEAL_GROW,
    _root_.libc_1.unix.linux_like.F_SEAL_SEAL, lift, bind_ok]
  rw [show ((0#i32 ||| 0x0002#i32) ||| 0x0004#i32) ||| 0x0001#i32 = finalizeSeals from hseals]
  step as ⟨r, shm1, hadded⟩
  rcases r with _ | e <;>
    simp only [core.result.Result.map_err, bind_ok, bind_tc_ok, WP.spec_ok,
      guest_memory.Error.MemoryAddSealsFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      guest_memory.Error.MemoryAddSealsFailed.constructor] <;>
    exact ⟨_, hadded, rfl, rfl⟩

end vm_memory.guest_memory.GuestMemory
