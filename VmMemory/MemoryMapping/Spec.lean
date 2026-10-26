module
public import VmMemory.Funs
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.base.mmap (Protection)
local notation "MmapError" => vm_memory.base.mmap.Error

namespace base.sys.linux.mmap.MemoryMapping

/-- Contract of the external creation operations. A normal error retains its
    value; success establishes the mapping's logical metadata. Correspondence
    of this metadata with unsafe Rust and the OS is an external assumption. -/
def CreationOutcome (size : Usize) (backing : MappingBacking) (protection : Protection)
    (status : core.result.Result Unit MmapError)
    (result : core.result.Result MemoryMapping MmapError) : Prop :=
  match status with
  | .Ok _ => ∃ mapping, result = .Ok mapping ∧
      mapping.length = size ∧ mapping.backing = backing ∧
      mapping.readable = protection.read ∧ mapping.writable = protection.write
  | .Err error => result = .Err error

theorem CreationOutcome.success {size : Usize} {backing : MappingBacking}
    {protection : Protection} {status : core.result.Result Unit MmapError} {mapping : MemoryMapping}
    (h : CreationOutcome size backing protection status (.Ok mapping)) :
    mapping.length = size ∧ mapping.backing = backing ∧
      mapping.readable = protection.read ∧ mapping.writable = protection.write := by
  cases status <;> simp_all [CreationOutcome]

theorem CreationOutcome.error {size : Usize} {backing : MappingBacking}
    {protection : Protection} {error : MmapError} {result : core.result.Result MemoryMapping MmapError}
    (h : CreationOutcome size backing protection (.Err error) result) :
    result = .Err error := h

private theorem creation_result_outcome (size : Usize) (backing : MappingBacking)
    (protection : Protection) (status : core.result.Result Unit MmapError) :
    CreationOutcome size backing protection status (creation_result size backing protection status) := by
  cases status <;> simp [CreationOutcome, creation_result]

@[step]
theorem new_protection_spec (size : Usize) (align : Option U64) (protection : Protection)
    (status : core.result.Result Unit MmapError)
    (hStatus : new_protection_status size align protection = ok status) :
    new_protection size align protection ⦃ result =>
      CreationOutcome size .anonymous protection status result ⦄ := by
  simp only [new_protection, hStatus, bind_ok, WP.spec_ok]
  exact creation_result_outcome _ _ _ _

@[step]
theorem from_fd_offset_protection_populate_spec
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    (status : core.result.Result Unit MmapError)
    (hStatus : from_fd_offset_protection_populate_status
      descriptor size offset align protection populate = ok status) :
    from_fd_offset_protection_populate descriptor size offset align protection populate ⦃ result =>
      CreationOutcome size (.descriptor (descriptor_backing descriptor) offset)
        protection status result ⦄ := by
  simp only [from_fd_offset_protection_populate, hStatus, bind_ok, WP.spec_ok]
  exact creation_result_outcome _ _ _ _

/-- External failures are distinct from normally returned Rust errors. -/
theorem new_protection_failure (size : Usize) (align : Option U64) (protection : Protection)
    (error : Aeneas.Std.Error)
    (hStatus : new_protection_status size align protection = fail error) :
    new_protection size align protection = fail error := by
  simp [new_protection, hStatus]

theorem from_fd_offset_protection_populate_failure
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : Protection) (populate : Bool)
    (error : Aeneas.Std.Error)
    (hStatus : from_fd_offset_protection_populate_status
      descriptor size offset align protection populate = fail error) :
    from_fd_offset_protection_populate descriptor size offset align protection populate = fail error := by
  simp [from_fd_offset_protection_populate, hStatus]

end base.sys.linux.mmap.MemoryMapping
