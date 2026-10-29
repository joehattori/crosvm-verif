module
public import Syscalls.MappingState
@[expose] public section
open Aeneas Aeneas.Std Result
open Utils.Alignment Syscalls.Mmap

namespace Syscalls.Mmap.Tests

private def reservation : Mapping :=
  { addr := { addr := 4096#usize }, size := 12288#usize }

private def afterPrefix : Mapping :=
  { addr := { addr := 8192#usize }, size := 8192#usize }

private def kept : Mapping :=
  { addr := { addr := 8192#usize }, size := 4096#usize }

private def removedPrefix : Mapping :=
  { addr := reservation.addr, size := 4096#usize }

-- The syscall contract itself yields the updated mapping after a successful trim.
example (ret : I32) (after : MappingState)
    (h : MunmapCallSpec 4096#usize reservation.state removedPrefix ret after) (hz : ret = 0#i32) :
    after = afterPrefix.state := by
  apply h.prefix hz <;> norm_num [reservation, afterPrefix, removedPrefix]

-- The removed prefix is no longer available to justify a subsequent allocated trim.
example (ret : I32) (after : MappingState)
    (h : MunmapCallSpec 4096#usize reservation.state removedPrefix ret after) (hz : ret = 0#i32) :
    ¬after.Covers removedPrefix := by
  intro hcovered
  have hp : removedPrefix.state 4096 := by norm_num [Mapping.state, intervalState, removedPrefix, reservation]
  exact h.removed_unmapped hz 4096 hp (hcovered 4096 hp)

-- An address range alone cannot establish the contract for bytes that are not mapped.
example (ret : I32) (after : MappingState) :
    ¬MunmapCallSpec 4096#usize afterPrefix.state removedPrefix ret after := by
  intro h
  have hp := h.allocated 4096 (by norm_num [Mapping.state, intervalState, removedPrefix, reservation])
  norm_num [Mapping.state, intervalState, afterPrefix] at hp

-- [4096,16384) minus [4096,8192) is the updated record [8192,16384).
example : unmapEffect 4096#usize reservation.state { addr := 4096#usize }
    4096#usize 0#i32 = afterPrefix.state := by
  apply unmapEffect_prefix <;> norm_num [reservation, afterPrefix]

-- The second trim consumes the first trim's resulting state.
example : unmapEffect 4096#usize
    (unmapEffect 4096#usize reservation.state { addr := 4096#usize } 4096#usize 0#i32)
    { addr := 12288#usize } 4096#usize 0#i32 = kept.state := by
  have hp : unmapEffect 4096#usize reservation.state { addr := 4096#usize }
      4096#usize 0#i32 = afterPrefix.state := by
    apply unmapEffect_prefix <;> norm_num [reservation, afterPrefix]
  rw [hp]
  apply unmapEffect_suffix <;> norm_num [afterPrefix, kept]

-- A failed syscall must not be credited with releasing any bytes.
example : unmapEffect 4096#usize reservation.state { addr := 4096#usize }
    4096#usize (-1)#i32 = reservation.state := by
  apply unmapEffect_failure
  decide

-- Unmapping one byte removes its whole page, not just that byte.
example : ¬unmapEffect 4096#usize reservation.state { addr := 4096#usize }
    1#usize 0#i32 8191 := by
  norm_num [unmapEffect, alignUp]

-- An overlong prefix destroys part of the intended retained mapping.
example : ¬(unmapEffect 4096#usize reservation.state { addr := 4096#usize }
    8192#usize 0#i32).Covers kept := by
  intro h
  have hp := h 8192 (by norm_num [Mapping.state, intervalState, kept])
  norm_num [unmapEffect, alignUp] at hp

-- A suffix starting inside a page cannot be reported as successfully unmapped.
example (ret : I32)
    (h : MunmapReturnSpec 4096#usize { addr := 12289#usize } 4095#usize ret) :
    ret ≠ 0#i32 := by
  intro hz
  have hmod := (h.2 hz).2.1
  norm_num at hmod

end Syscalls.Mmap.Tests
