module
public import VmMemory.Types
@[expose] public section
open Aeneas Aeneas.Std Result

/-- Model the stable length returned by MappedRegion::size. This is the only
    mapping operation used by the extracted interval queries. -/
@[rust_fun "base::mmap::{base::mmap::MappedRegion<base::mmap::MemoryMapping>}::size"]
def base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size
    (self : base.mmap.MemoryMapping) : Result Usize :=
  ok self.length
