module
public import Syscalls.Mmap
@[expose] public section
open Aeneas Aeneas.Std Result
open Syscalls.Mmap

namespace Syscalls.Mmap.Tests

/-! Kernel-checked examples of the ownership tokens with 4 KiB pages and the
    reservation `[4096, 16384)`. -/

private def reservation : Mapping :=
  { addr := { addr := 4096#usize }, size := 12288#usize }

private def afterPrefix : Mapping :=
  { addr := { addr := 8192#usize }, size := 8192#usize }

private def kept : Mapping :=
  { addr := { addr := 8192#usize }, size := 4096#usize }

-- Unmapping the prefix `[4096, 8192)` leaves `[8192, 16384)`.
example : reservation.CanTrim 4096#usize { addr := 4096#usize } 4096#usize ∧
    reservation.trim { addr := 4096#usize } 4096#usize = afterPrefix := by
  refine ⟨by norm_num [Mapping.CanTrim, reservation], ?_⟩
  obtain ⟨ha, hs⟩ := Mapping.trim_prefix (tok := reservation) (addr := { addr := 4096#usize })
    (len := 4096#usize) (by norm_num [reservation]) (by norm_num [reservation])
    (by norm_num [Usize.max_def, Usize.numBits_def]; cases System.Platform.numBits_eq <;> simp_all)
  exact Mapping.ext_val (by rw [ha]; rfl) (by rw [hs]; rfl)

-- The suffix `[12288, 16384)` is then unmapped from the token the first call left.
example : afterPrefix.CanTrim 4096#usize { addr := 12288#usize } 4096#usize ∧
    afterPrefix.trim { addr := 12288#usize } 4096#usize = kept := by
  refine ⟨by norm_num [Mapping.CanTrim, afterPrefix], ?_⟩
  obtain ⟨ha, hs⟩ := Mapping.trim_suffix (tok := afterPrefix) (addr := { addr := 12288#usize })
    (len := 4096#usize) (by norm_num [afterPrefix]) (by norm_num [afterPrefix])
  exact Mapping.ext_val (by rw [ha]; rfl) (by rw [hs]; rfl)

-- A successful `munmap` passes on the trimmed token; a failed one keeps the token.
example (ret : I32)
    (hm : _root_.libc_1.unix.munmap { addr := 4096#usize } 4096#usize = ok ret) :
    munmapGhost 4096#usize (some reservation) { addr := 4096#usize } 4096#usize =
      ok (ret, some (if ret = 0#i32 then reservation.trim { addr := 4096#usize } 4096#usize
        else reservation)) := by
  have hcan : reservation.CanTrim 4096#usize { addr := 4096#usize } 4096#usize := by
    norm_num [Mapping.CanTrim, reservation]
  simp only [munmapGhost, hm, bind_ok, if_pos hcan]

-- The prefix is no longer owned after it was unmapped, so unmapping it again
-- loses the token.
example (ret : I32)
    (hm : _root_.libc_1.unix.munmap { addr := 4096#usize } 4096#usize = ok ret) :
    munmapGhost 4096#usize (some afterPrefix) { addr := 4096#usize } 4096#usize =
      ok (ret, none) := by
  have hcan : ¬afterPrefix.CanTrim 4096#usize { addr := 4096#usize } 4096#usize := by
    norm_num [Mapping.CanTrim, afterPrefix]
  simp only [munmapGhost, hm, bind_ok, if_neg hcan]

-- A range in the middle would split the token, so it is not a valid trim.
example : ¬reservation.CanTrim 4096#usize { addr := 8192#usize } 4096#usize := by
  norm_num [Mapping.CanTrim, reservation]

-- A prefix ending inside a page is not a valid trim: `munmap` would also
-- remove the rest of that page.
example : ¬reservation.CanTrim 4096#usize { addr := 4096#usize } 1#usize := by
  norm_num [Mapping.CanTrim, reservation]

-- `MAP_FIXED` outside the owned token loses the token.
example (ret : VoidPtr)
    (hm : _root_.libc_1.unix.linux_like.mmap64 { addr := 4096#usize } 4096#usize 0#i32
      MAP_FIXED (-1)#i32 0#i64 = ok ret) :
    mmapFixedGhost (some kept) { addr := 4096#usize } 4096#usize 0#i32 MAP_FIXED
      (-1)#i32 0#i64 = ok (ret, none) := by
  have hout : ¬kept.Contains
      { addr := RawPtr.cast _ .Mut ({ addr := 4096#usize } : VoidPtr), size := 4096#usize } := by
    norm_num [Mapping.Contains, kept]
  simp only [mmapFixedGhost, hm, bind_ok, if_neg hout]

end Syscalls.Mmap.Tests
