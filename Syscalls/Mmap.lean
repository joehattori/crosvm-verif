module
public import VmMemory.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory

namespace Syscalls.Mmap

abbrev VoidPtr := MutRawPtr vm_memory.core.ffi.c_void

/-- Null `*mut c_void` pointer (`0usize as *mut c_void`). -/
abbrev nullVoidPtr : VoidPtr := { addr := 0#usize }

/-- Sentinel returned by `mmap64` on failure (`!0usize as *mut c_void`). -/
abbrev mapFailedPtr : VoidPtr := { addr := core.num.Usize.MAX }

/-- Page can be read (`0x0001`). -/
abbrev PROT_READ : I32 := 0x0001#i32

/-- Page can be written (`0x0002`). -/
abbrev PROT_WRITE : I32 := 0x0002#i32

/-- Share changes (`0x0001`). -/
abbrev MAP_SHARED : I32 := 0x0001#i32

/-- Changes are private (`0x0002`). -/
abbrev MAP_PRIVATE : I32 := 0x0002#i32

/-- Interpret `addr` exactly (`0x0010`). -/
abbrev MAP_FIXED : I32 := 0x0010#i32

/-- Don't use a file (`0x0020`). -/
abbrev MAP_ANONYMOUS : I32 := 0x0020#i32

/-- Don't check for reservations (`0x4000`). -/
abbrev MAP_NORESERVE : I32 := 0x4000#i32

/-- Populate (prefault) pagetables (`0x8000`). -/
abbrev MAP_POPULATE : I32 := 0x8000#i32

/-- `fcntl` command to query file seals (`F_LINUX_SPECIFIC_BASE + 10`). -/
abbrev F_GET_SEALS : I32 := 1034#i32

/-- File seal preventing writes (`0x0008`). -/
abbrev F_SEAL_WRITE : I32 := 0x0008#i32

/-- Outcome of a single `mmap64(2)` system call at `(reqAddr, size, prot, flags, fd, offset)`:
    `mmap64` returns `ret : VoidPtr`, which is either `mapFailedPtr` (`MAP_FAILED`) on
    failure, or a valid mapped address whose range `[ret, ret + size)` fits in the
    user address space without wrapping, equals `reqAddr` when `MAP_FIXED` is set in
    `flags`, and is page-aligned when `reqAddr` is null. -/
def MmapCallSpec (pageSize : Usize) (reqAddr : VoidPtr) (size : Usize)
    (prot flags fd : I32) (offset : I64) (ret : VoidPtr) : Prop :=
  _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot flags fd offset = ok ret ∧
  (ret ≠ mapFailedPtr →
    ret.addr.val + size.val ≤ Usize.max ∧
    (flags &&& MAP_FIXED ≠ 0#i32 → ret = reqAddr) ∧
    (reqAddr = nullVoidPtr → ret.addr.val % pageSize.val = 0))

/-- System-level specification of `libc::mmap64`: every call to `mmap64`
    returns a pointer `ret` satisfying `MmapCallSpec`. -/
def MmapSpec (pageSize : Usize) : Prop :=
  ∀ reqAddr size prot flags fd offset,
    ∃ ret, MmapCallSpec pageSize reqAddr size prot flags fd offset ret

end Syscalls.Mmap
