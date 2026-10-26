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

namespace base.sys.linux.mmap

/-- Logical provenance at creation. A descriptor-backed mapping records the
    backing object's identity, not a reusable numeric file descriptor. Files and
    shared memory both use this variant; it does not imply MAP_SHARED semantics. -/
inductive MappingBacking where
  | anonymous
  | descriptor (objectId : Nat) (offset : U64)

/-- External platform mapping with logical metadata. Its length corresponds to
    Rust's stored size; backing and protection are ghost fields supplied by the
    external creation contracts. Their correspondence to the OS is trusted.
    This does not model contents, pointers, access safety, ownership, or lifetime. -/
@[rust_type "base::sys::linux::mmap::MemoryMapping"]
structure MemoryMapping where
  length : Usize
  backing : MappingBacking
  readable : Bool
  writable : Bool

end base.sys.linux.mmap

/-- Unobserved by the verified queries; equality and operations are not modeled. -/
def guest_memory.BackingObject := Unit

def guest_memory.MemoryRegionOptions := Unit
