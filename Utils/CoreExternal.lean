module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Handwritten models of Rust core library functions used by more than one
    extracted crate. Aeneas names these items without a crate prefix, so each
    may be defined only once across the library. -/

/-- Apply the closure only to a present value, propagating its optional result. -/
@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
def core.option.Option.and_then {T U F : Type _}
    (fnInst : core.ops.function.FnOnce F T (Option U))
    (value : Option T) (f : F) : Result (Option U) :=
  match value with
  | none => ok none
  | some x => fnInst.call_once f x

/-- Apply the closure on success; preserve errors without calling it. -/
@[rust_fun "core::result::{core::result::Result<@T, @E>}::map"]
def core.result.Result.map {T E U F : Type _} (f : core.ops.function.FnOnce F T U)
    (self : core.result.Result T E) (closure : F) : Result (core.result.Result U E) := do
  match self with
  | .Ok value =>
    let mapped ← f.call_once closure value
    ok (.Ok mapped)
  | .Err error => ok (.Err error)

/-- Rust's default lazy map adapter. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::map"]
def core.iter.traits.iterator.Iterator.map.default {I F T B : Type _}
    (_iter : core.iter.traits.iterator.Iterator I T) (_f : core.ops.function.FnMut F T B)
    (iter : I) (f : F) : Result (core.iter.adapters.map.Map I F) := ok ⟨iter, f⟩

@[rust_fun
  "core::iter::adapters::map::{core::iter::traits::iterator::Iterator<core::iter::adapters::map::Map<@I, @F>, @B>}::next"]
def core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next
    {B I F T : Type _} (iterInst : core.iter.traits.iterator.Iterator I T)
    (fInst : core.ops.function.FnMut F T B) (self : core.iter.adapters.map.Map I F) :
    Result (Option B × core.iter.adapters.map.Map I F) := do
  let (item, iter) ← iterInst.next self.iter
  match item with
  | none => ok (none, ⟨iter, self.f⟩)
  | some x =>
    let (y, f) ← fInst.call_mut self.f x
    ok (some y, ⟨iter, f⟩)

/-- The non-strict relation of a pure comparator, used by the stable-sort model. -/
noncomputable def alloc.slice.sortLe {T F : Type _}
    (cmp : core.ops.function.FnMut F (T × T) Ordering) (closure : F) (x y : T) : Bool := by
  classical
  exact decide (cmp.call_mut closure (x, y) ≠ ok (.gt, closure))

/-- Stable sorting for pure, nonfailing total comparators. Stateful, failing, or
    inconsistent comparators are unsupported and fail explicitly. Merge sort
    preserves equal-key order, as Rust's `sort_by` requires; the Rust sorting
    algorithm and allocation failures are abstracted away. -/
@[rust_fun "alloc::slice::{[@T]}::sort_by"]
noncomputable def alloc.slice.Slice.sort_by {T F : Type _}
    (cmp : core.ops.function.FnMut F (T × T) Ordering) (self : Slice T) (closure : F) :
    Result (Slice T) := by
  classical
  let le := alloc.slice.sortLe cmp closure
  exact if
    (∀ x y, ∃ order, cmp.call_mut closure (x, y) = ok (order, closure) ∧
      cmp.call_mut closure (y, x) = ok (order.swap, closure)) ∧
    (∀ x y z, le x y → le y z → le x z)
  then ok (Slice.from (self.val.mergeSort le) (by simp))
  else fail .panic

/-- Return `true` for `None`; apply the closure to a present value. -/
@[rust_fun "core::option::{core::option::Option<@T>}::is_none_or"]
def core.option.Option.is_none_or {T F : Type _} (fnInst : core.ops.function.FnOnce F T Bool)
    (self : Option T) (f : F) : Result Bool :=
  match self with
  | none => ok true
  | some x => fnInst.call_once f x

/-- Clone a present value with the element's `Clone`. -/
@[rust_fun "core::option::{core::clone::Clone<core::option::Option<@T>>}::clone"]
def core.option.Option.Insts.CoreCloneClone.clone {T : Type _} (cloneInst : core.clone.Clone T)
    (self : Option T) : Result (Option T) :=
  match self with
  | none => ok none
  | some x => do
    let y ← cloneInst.clone x
    ok (some y)

/-- The last element of a slice, if any. -/
@[reducible, rust_fun "core::slice::{[@T]}::last"]
def core.slice.Slice.last {T : Type _} (s : Slice T) : Result (Option T) :=
  ok s.val.getLast?

/-- The blanket `TryFrom<U> for T` where `U: Into<T>` never fails. -/
@[rust_fun "core::convert::{core::convert::TryFrom<@T, @U, !>}::try_from"]
def core.convert.TryFromTUNever.Blanket.try_from {T U : Type _} (intoInst : core.convert.Into U T)
    (u : U) : Result (core.result.Result T Never) := do
  let t ← intoInst.into u
  ok (.Ok t)

/-- `usize::try_from(u64)` fails when the value doesn't fit in `usize`. -/
@[reducible, rust_fun
  "core::convert::num::ptr_try_from_impls::{core::convert::TryFrom<usize, u64, core::num::error::TryFromIntError>}::try_from"]
def Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from (i : U64) :
    Result (core.result.Result Usize core.num.error.TryFromIntError) :=
  core.num.tryFromUScalar .Usize i

/-- Formatting is not modeled: write nothing and succeed. -/
@[reducible, rust_fun "core::num::error::{core::fmt::Debug<core::num::error::TryFromIntError>}::fmt"]
def core.num.error.TryFromIntError.Insts.CoreFmtDebug.fmt (_ : core.num.error.TryFromIntError)
    (fmt : core.fmt.Formatter) :
    Result ((core.result.Result Unit core.fmt.Error) × core.fmt.Formatter) :=
  ok (.Ok (), fmt)
