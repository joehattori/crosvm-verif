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
