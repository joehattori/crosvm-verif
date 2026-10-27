module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-- Abstract identity of an I/O error. Only preservation through mapping errors
    is modeled; error inspection and formatting are outside this slice. -/
@[rust_type "core::io::error::Error"]
structure core.io.error.Error where
  identity : Nat

/-- The stored errno value; no host error lookup is modeled. -/
@[rust_type "base::errno::Error"]
structure base.errno.Error where
  errno : I32

/-- Logical file identity and its Linux descriptor while borrowed. Correspondence
    with Rust's File is assumed; contents, ownership, close, and descriptor reuse
    are not modeled. Builder setters retain this value without inspecting it. -/
@[rust_type "std::fs::File"]
structure std.fs.File where
  identity : Nat
  descriptor : I32

/-- Unobserved by the verified queries; equality and operations are not modeled. -/
def guest_memory.BackingObject := Unit

def guest_memory.MemoryRegionOptions := Unit
