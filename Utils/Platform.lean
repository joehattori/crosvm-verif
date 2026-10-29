module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

/-- crosvm supports only 64-bit hosts (x86_64, aarch64, riscv64): 32-bit hosts
    were dropped upstream. The generated Lean is platform-generic, as `Usize` has
    `System.Platform.numBits` bits, which Lean only knows to be 32 or 64. Specs
    that rely on the 64-bit width take `[Platform64]` instead of per-value fit
    hypotheses. -/
class Platform64 : Prop where
  numBits_eq : System.Platform.numBits = 64

namespace Platform64

theorem usize_max_eq [Platform64] : Usize.max = U64.max := by
  simp only [Usize.max, Usize.numBits, UScalarTy.numBits, numBits_eq, U64.max, U64.numBits]

theorem val_le_usize_max [Platform64] (x : U64) : x.val ≤ Usize.max := by
  have := x.hBounds
  rw [usize_max_eq]
  scalar_tac

/-- Casting `u64` to `usize` is lossless. -/
theorem u64_cast_usize_val [Platform64] (x : U64) : (UScalar.cast .Usize x).val = x.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  have := val_le_usize_max x
  scalar_tac

end Platform64
