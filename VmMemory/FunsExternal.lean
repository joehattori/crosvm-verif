module
public import VmMemory.Types
@[expose] public section
open Aeneas Aeneas.Std Result

/-- Descriptor accessor stored in the file's trait instance. The builder
    configuration methods package this instance but do not call the accessor. -/
@[rust_fun
  "base::sys::unix::descriptor::{base::descriptor::AsRawDescriptor<std::fs::File>}::as_raw_descriptor"]
def std.fs.File.Insts.BaseDescriptorAsRawDescriptor.as_raw_descriptor
    (self : std.fs.File) : Result I32 :=
  ok self.descriptor

/-- Logical length of the platform mapping carried by the translated wrapper. -/
abbrev vm_memory.base.mmap.MemoryMapping.length
    (self : vm_memory.base.mmap.MemoryMapping) : Usize := self.mapping.length

/-- Model the stable length returned by MappedRegion::size. -/
@[rust_fun "base::mmap::{base::mmap::MappedRegion<base::mmap::MemoryMapping>}::size"]
def base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size
    (self : vm_memory.base.mmap.MemoryMapping) : Result Usize :=
  ok self.length

/-- Descriptor cloning is outside the verified wrap(_, None) path used by build.
    No behavior or normal termination is assumed for this opaque operation. -/
@[rust_fun
  "base::descriptor::{core::convert::TryFrom<base::descriptor::SafeDescriptor, &'0 @, core::io::error::Error>}::try_from"]
opaque base.descriptor.SafeDescriptor.Insts.CoreConvertTryFromShared0PError.try_from
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor) :
    Result (core.result.Result vm_memory.base.descriptor.SafeDescriptor core.io.error.Error) :=
  fail .panic

/-- Host error lookup, only reached by wrap's descriptor-cloning branch. -/
@[rust_fun "base::errno::{base::errno::Error}::last"]
opaque base.errno.Error.last : Result base.errno.Error := fail .panic

namespace base.sys.linux.mmap.MemoryMapping

/-- Ghost identity of the OS object designated by this descriptor during a
    creation invocation. Correspondence with the live object is trusted; the
    opaque witness supplies no facts about identity, validity, or descriptor
    reuse. In particular this is not the numeric file descriptor. -/
opaque descriptor_backing (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor) : Nat := 0

/-- External response of anonymous mapping creation, including validation and OS
    errors. The opaque witness only inhabits the model: proofs assume an observed
    response and cannot infer allocation success or normal termination. -/
opaque new_protection_status (size : Usize) (align : Option U64)
    (protection : vm_memory.base.mmap.Protection) :
    Result (core.result.Result Unit vm_memory.base.mmap.Error) :=
  fail .panic

/-- External response for one descriptor-backed mapping invocation. All arguments
    are retained, including defaults selected by the translated builder. These
    oracles do not model changing OS state or repeated allocation histories. -/
opaque from_fd_offset_protection_populate_status
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : vm_memory.base.mmap.Protection)
    (populate : Bool) : Result (core.result.Result Unit vm_memory.base.mmap.Error) :=
  fail .panic

/-- Materialize the metadata promised by a successful external mapping operation.
    Length, provenance, and protection correspondence are trusted. This asserts
    no memory contents, ownership, access safety, or mapping lifetime. -/
def creation_result (size : Usize) (backing : MappingBacking)
    (protection : vm_memory.base.mmap.Protection)
    (status : core.result.Result Unit vm_memory.base.mmap.Error) :
    core.result.Result MemoryMapping vm_memory.base.mmap.Error :=
  match status with
  | .Ok _ => .Ok {
      length := size, backing := backing,
      readable := protection.read, writable := protection.write }
  | .Err error => .Err error

@[rust_fun
  "base::sys::linux::mmap::{base::sys::linux::mmap::MemoryMapping}::new_protection"]
def new_protection (size : Usize) (align : Option U64)
    (protection : vm_memory.base.mmap.Protection) :
    Result (core.result.Result MemoryMapping vm_memory.base.mmap.Error) := do
  let status ← new_protection_status size align protection
  ok (creation_result size .anonymous protection status)

@[rust_fun
  "base::sys::linux::mmap::{base::sys::linux::mmap::MemoryMapping}::from_fd_offset_protection_populate"]
def from_fd_offset_protection_populate
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor)
    (size : Usize) (offset align : U64) (protection : vm_memory.base.mmap.Protection)
    (populate : Bool) : Result (core.result.Result MemoryMapping vm_memory.base.mmap.Error) := do
  let status ← from_fd_offset_protection_populate_status descriptor size offset align protection populate
  ok (creation_result size (.descriptor (descriptor_backing descriptor) offset) protection status)

end base.sys.linux.mmap.MemoryMapping
