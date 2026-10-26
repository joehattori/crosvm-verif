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

/-- Model the stable length returned by MappedRegion::size. This is the only
    mapping operation used by the extracted interval queries. -/
@[rust_fun "base::mmap::{base::mmap::MappedRegion<base::mmap::MemoryMapping>}::size"]
def base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size
    (self : base.mmap.MemoryMapping) : Result Usize :=
  ok self.length
