module
public import Utils.CoreExternal
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Specifications of the shared core models in `Utils/CoreExternal.lean`. -/

/-- `sort_by` with a pure comparator that compares natural-number keys sorts
    stably by key. -/
theorem alloc.slice.Slice.sort_by_key_spec {T F : Type _}
    (cmp : core.ops.function.FnMut F (T × T) Ordering) (closure : F) (key : T → Nat)
    (hcmp : ∀ x y, cmp.call_mut closure (x, y) = ok (compare (key x) (key y), closure))
    (s : Slice T) :
    alloc.slice.Slice.sort_by cmp s closure ⦃ sorted =>
      sorted.val = s.val.mergeSort (fun a b => key a ≤ key b) ⦄ := by
  have hle : alloc.slice.sortLe cmp closure = (fun a b => decide (key a ≤ key b)) := by
    funext x y
    unfold alloc.slice.sortLe
    rw [hcmp]
    simp [Nat.compare_ne_gt]
  have hpure : ∀ x y, ∃ order, cmp.call_mut closure (x, y) = ok (order, closure) ∧
      cmp.call_mut closure (y, x) = ok (order.swap, closure) :=
    fun x y => ⟨compare (key x) (key y), hcmp x y, by rw [hcmp, Nat.compare_swap]⟩
  have htrans : ∀ x y z, alloc.slice.sortLe cmp closure x y →
      alloc.slice.sortLe cmp closure y z → alloc.slice.sortLe cmp closure x z := by
    simp only [hle, decide_eq_true_eq]
    exact fun _ _ _ => Nat.le_trans
  unfold alloc.slice.Slice.sort_by
  rw [ite_eq_left ⟨hpure, htrans⟩]
  simp only [WP.spec_ok, Slice.from_val, hle]
