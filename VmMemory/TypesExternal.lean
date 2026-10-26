module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/- These models support only MemoryRegion's interval queries. Correspondence
   with Rust is assumed: the mapping stores its stable logical byte length.
   Pointers, contents, permissions, allocation, and mapping lifetime are outside
   this model. Unobserved backing objects and options are erased; their equality
   and operations are not modeled. -/

@[rust_type "base::mmap::MemoryMapping"]
structure base.mmap.MemoryMapping where
  length : Usize

def guest_memory.BackingObject := Unit

def guest_memory.MemoryRegionOptions := Unit
