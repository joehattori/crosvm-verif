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
    failure, or an address whose numeric range `[ret, ret + size)` fits in `usize`
    without wrapping, equals `reqAddr` when `MAP_FIXED` is set in `flags`, and is
    page-aligned on success, with a positive page size. This return-value model does not represent
    the OS memory state, ownership, contents, or access permissions. -/
def MmapCallSpec (pageSize : Usize) (reqAddr : VoidPtr) (size : Usize)
    (prot flags fd : I32) (offset : I64) (ret : VoidPtr) : Prop :=
  _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot flags fd offset = ok ret ∧
  (ret ≠ mapFailedPtr →
    ret.addr.val + size.val ≤ Usize.max ∧
    (flags &&& MAP_FIXED ≠ 0#i32 → ret = reqAddr) ∧
    (0 < pageSize.val ∧ ret.addr.val % pageSize.val = 0))

/-- System-level specification of `libc::mmap64`: every call to `mmap64`
    returns a pointer `ret` satisfying `MmapCallSpec`. -/
def MmapSpec (pageSize : Usize) : Prop :=
  ∀ reqAddr size prot flags fd offset,
    ∃ ret, MmapCallSpec pageSize reqAddr size prot flags fd offset ret

/-- System-level specification of `libc::munmap`: every call returns a C
    status. Its effect on owned memory is modeled by `munmapGhost`. -/
def MunmapSpec : Prop :=
  ∀ addr len, ∃ ret, _root_.libc_1.unix.munmap addr len = ok ret

/-! ### Ownership tokens

A function that maps memory owns the region `mmap64` returned and must not
touch memory it does not own. `mmapGhost`, `mmapFixedGhost`, and `munmapGhost`
wrap the system calls and pass a ghost token, the `Mapping` record of the
owned region, from call to call. A caller that only needs the result can drop
the token; dropping it from the wrappers gives back the plain calls. `none`
means that no region is owned: either nothing was mapped yet, or a call
touched memory outside the token. -/

abbrev Mapping := vm_memory.base.sys.linux.mmap.MemoryMapping

/-- `inner` lies within `outer`: `[inner.addr, inner.addr + inner.size)` is a
    subrange of `[outer.addr, outer.addr + outer.size)`. -/
def Mapping.Contains (outer inner : Mapping) : Prop :=
  outer.addr.addr.val ≤ inner.addr.addr.val ∧
  inner.addr.addr.val + inner.size.val ≤ outer.addr.addr.val + outer.size.val

instance (outer inner : Mapping) : Decidable (outer.Contains inner) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem Mapping.Contains.trans {a b c : Mapping} (hab : a.Contains b) (hbc : b.Contains c) :
    a.Contains c := by
  unfold Mapping.Contains at *
  omega

theorem Mapping.ext_val {a b : Mapping} (haddr : a.addr.addr.val = b.addr.addr.val)
    (hsize : a.size.val = b.size.val) : a = b := by
  rcases a with ⟨⟨a⟩, s⟩
  rcases b with ⟨⟨b⟩, t⟩
  have h1 : a = b := UScalar.eq_of_val_eq haddr
  have h2 : s = t := UScalar.eq_of_val_eq hsize
  subst h1 h2
  rfl

/-- `[addr, addr + len)` can be unmapped from the token `tok` while keeping one
    contiguous region: it is non-empty and either a prefix of `tok` that ends
    on a page boundary or a suffix of `tok`. `munmap` removes whole pages, so a
    prefix ending inside a page would also remove the start of the rest. A
    suffix end is rounded up within the pages that `mmap64` mapped for `tok`. -/
def Mapping.CanTrim (pageSize : Usize) (tok : Mapping) (addr : VoidPtr) (len : Usize) : Prop :=
  0 < len.val ∧ len.val ≤ tok.size.val ∧
  ((addr.addr = tok.addr.addr ∧ (addr.addr.val + len.val) % pageSize.val = 0) ∨
    addr.addr.val + len.val = tok.addr.addr.val + tok.size.val)

instance (pageSize : Usize) (tok : Mapping) (addr : VoidPtr) (len : Usize) :
    Decidable (tok.CanTrim pageSize addr len) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ (_ ∨ _)))

/-- The region left after unmapping `[addr, addr + len)` from `tok`: the start
    of `tok` when the range is a suffix, and the end of `tok` otherwise. -/
def Mapping.trim (tok : Mapping) (addr : VoidPtr) (len : Usize) : Mapping :=
  if addr.addr.val + len.val = tok.addr.addr.val + tok.size.val then
    { addr := tok.addr, size := core.num.Usize.wrapping_sub tok.size len }
  else
    { addr := { addr := core.num.Usize.wrapping_add addr.addr len },
      size := core.num.Usize.wrapping_sub tok.size len }

/-- `mmap64` for a new mapping: on success the caller owns `[ret, ret + size)`. -/
def mmapGhost (reqAddr : VoidPtr) (size : Usize) (prot flags fd : I32) (offset : I64) :
    Result (VoidPtr × Option Mapping) := do
  let ret ← _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot flags fd offset
  ok (ret, if ret = mapFailedPtr then none else some { addr := RawPtr.cast _ .Mut ret, size })

/-- `mmap64` with `MAP_FIXED` at `reqAddr`. It replaces whatever is mapped in
    `[reqAddr, reqAddr + size)`, so the range must lie in the owned token,
    which stays owned. -/
def mmapFixedGhost (owned : Option Mapping) (reqAddr : VoidPtr) (size : Usize)
    (prot flags fd : I32) (offset : I64) : Result (VoidPtr × Option Mapping) := do
  let ret ← _root_.libc_1.unix.linux_like.mmap64 reqAddr size prot flags fd offset
  ok (ret, match owned with
    | some tok => if tok.Contains { addr := RawPtr.cast _ .Mut reqAddr, size } then some tok else none
    | none => none)

/-- `munmap(addr, len)` on the owned token. A range that `CanTrim` the token
    leaves the trimmed token on success (`ret = 0`) and the same token on
    failure. Any other range touches memory the token does not cover. -/
def munmapGhost (pageSize : Usize) (owned : Option Mapping) (addr : VoidPtr) (len : Usize) :
    Result (I32 × Option Mapping) := do
  let ret ← _root_.libc_1.unix.munmap addr len
  ok (ret, match owned with
    | some tok =>
      if tok.CanTrim pageSize addr len then
        some (if ret = 0#i32 then tok.trim addr len else tok)
      else none
    | none => none)

private theorem usize_size_eq : UScalar.size .Usize = Usize.max + 1 := by
  have hpos : 0 < UScalar.size .Usize := by simp [UScalar.size_def]
  have hmax : Usize.max = UScalar.size .Usize - 1 := by
    rw [UScalar.size_def, Usize.max_def, Usize.numBits_def]
  omega

private theorem wrapping_sub_val_of_le {x y : Usize} (h : y.val ≤ x.val) :
    (core.num.Usize.wrapping_sub x y).val = x.val - y.val := by
  have hx : x.val ≤ Usize.max := by scalar_tac
  rw [core.num.Usize.wrapping_sub_val_eq, usize_size_eq,
    show x.val + (Usize.max + 1 - y.val) = (x.val - y.val) + (Usize.max + 1) by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

private theorem wrapping_add_val_of_le {x y : Usize} (h : x.val + y.val ≤ Usize.max) :
    (core.num.Usize.wrapping_add x y).val = x.val + y.val := by
  rw [core.num.Usize.wrapping_add_val_eq, usize_size_eq, Nat.mod_eq_of_lt (by omega)]

/-- Trimming a suffix keeps the start of the token. -/
theorem Mapping.trim_suffix {tok : Mapping} {addr : VoidPtr} {len : Usize}
    (hend : addr.addr.val + len.val = tok.addr.addr.val + tok.size.val)
    (hle : len.val ≤ tok.size.val) :
    (tok.trim addr len).addr = tok.addr ∧ (tok.trim addr len).size.val = tok.size.val - len.val := by
  simp only [Mapping.trim, hend, ↓reduceIte]
  exact ⟨trivial, wrapping_sub_val_of_le hle⟩

/-- Trimming a prefix keeps the end of the token. -/
theorem Mapping.trim_prefix {tok : Mapping} {addr : VoidPtr} {len : Usize}
    (hend : addr.addr.val + len.val ≠ tok.addr.addr.val + tok.size.val)
    (hle : len.val ≤ tok.size.val) (hfit : addr.addr.val + len.val ≤ Usize.max) :
    (tok.trim addr len).addr.addr.val = addr.addr.val + len.val ∧
      (tok.trim addr len).size.val = tok.size.val - len.val := by
  simp only [Mapping.trim, hend, ↓reduceIte]
  exact ⟨wrapping_add_val_of_le hfit, wrapping_sub_val_of_le hle⟩

/-- A trimmed token lies within the token it was trimmed from. -/
theorem Mapping.CanTrim.contains_trim {pageSize : Usize} {tok : Mapping} {addr : VoidPtr}
    {len : Usize} (h : tok.CanTrim pageSize addr len)
    (hfit : tok.addr.addr.val + tok.size.val ≤ Usize.max) :
    tok.Contains (tok.trim addr len) := by
  obtain ⟨_, hle, hcase⟩ := h
  unfold Mapping.Contains
  by_cases hend : addr.addr.val + len.val = tok.addr.addr.val + tok.size.val
  · obtain ⟨ha, hs⟩ := Mapping.trim_suffix hend hle
    rw [ha, hs]
    omega
  · rcases hcase with ⟨hp, _⟩ | hs
    · have hp' := congrArg UScalar.val hp
      obtain ⟨ha, hs⟩ := Mapping.trim_prefix hend hle (by omega)
      rw [ha, hs]
      omega
    · exact absurd hs hend

end Syscalls.Mmap
