module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-- Logical file identity and its Linux descriptor while borrowed. Correspondence
    with Rust's File is assumed; contents, ownership, close, and descriptor reuse
    are not modeled. Builder setters retain this value without inspecting it. -/
@[rust_type "std::fs::File"]
structure std.fs.File where
  identity : Nat
  descriptor : I32

/- The following models support MemoryRegion's interval queries. Correspondence
   with Rust is assumed: the mapping stores its stable logical byte length.
   Pointers, contents, permissions, allocation, and mapping lifetime are outside
   this model. Unobserved backing objects and options are erased; their equality
   and operations are not modeled. -/

@[rust_type "base::mmap::MemoryMapping"]
structure base.mmap.MemoryMapping where
  length : Usize

def guest_memory.BackingObject := Unit

def guest_memory.MemoryRegionOptions := Unit
