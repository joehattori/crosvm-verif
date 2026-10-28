module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Handwritten models of Rust core library functions used by more than one
    extracted crate. Aeneas names these items without a crate prefix, so each
    may be defined only once across the library. -/

/-- Apply the closure only to a present value, propagating its optional result. -/
@[rust_fun "core::option::{core::option::Option<@T>}::and_then"]
def core.option.Option.and_then {T U F : Type}
    (fnInst : core.ops.function.FnOnce F T (Option U))
    (value : Option T) (f : F) : Result (Option U) :=
  match value with
  | none => ok none
  | some x => fnInst.call_once f x
