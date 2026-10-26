module
public import VmMemory.Funs
@[expose] public section
open Aeneas Aeneas.Std Result

namespace vm_memory.base.mmap.MemoryMappingBuilder

/-- Initial configuration: the requested size and no optional settings. -/
def NewOutcome (size : Usize) (result : MemoryMappingBuilder) : Prop :=
  result = {
    descriptor := none
    is_file_descriptor := false
    size := size
    offset := none
    align := none
    protection := none
    populate := false
  }

/-- Select the supplied file and set the file flag, preserving every other field. -/
def FromFileOutcome (self : MemoryMappingBuilder) (file : _root_.std.fs.File)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with
    descriptor := some (Dyn.mk _ vm_memory.std.fs.File.Insts.BaseDescriptorAsRawDescriptor file)
    is_file_descriptor := true }

/-- Select the supplied shared memory, preserving every other field, including
    the existing file flag. -/
def FromSharedMemoryOutcome (self : MemoryMappingBuilder) (shm : base.shm.SharedMemory)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with
    descriptor := some (Dyn.mk _ base.shm.SharedMemory.Insts.BaseDescriptorAsRawDescriptor shm) }

/-- Set the explicit offset, preserving every other field. No validation occurs. -/
def OffsetOutcome (self : MemoryMappingBuilder) (offset : U64)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with offset := some offset }

@[step]
theorem new_spec (size : Usize) :
    MemoryMappingBuilder.new size ⦃ result => NewOutcome size result ⦄ := by
  simp [MemoryMappingBuilder.new, NewOutcome]

@[step]
theorem from_file_spec (self : MemoryMappingBuilder) (file : _root_.std.fs.File) :
    self.from_file file ⦃ result => FromFileOutcome self file result ⦄ := by
  simp [MemoryMappingBuilder.from_file, FromFileOutcome]

@[step]
theorem from_shared_memory_spec (self : MemoryMappingBuilder) (shm : base.shm.SharedMemory) :
    self.from_shared_memory shm ⦃ result => FromSharedMemoryOutcome self shm result ⦄ := by
  simp [MemoryMappingBuilder.from_shared_memory, FromSharedMemoryOutcome]

@[step]
theorem offset_spec (self : MemoryMappingBuilder) (offset : U64) :
    impl.offset self offset ⦃ result => OffsetOutcome self offset result ⦄ := by
  simp [impl.offset, OffsetOutcome]

end vm_memory.base.mmap.MemoryMappingBuilder
