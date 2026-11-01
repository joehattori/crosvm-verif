module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std
set_option linter.dupNamespace false

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

/-- Abstract path identity. Path contents, encoding, and operations are not
    modeled; the verified constructors only store the default `None` parameters. -/
@[rust_type "std::path::PathBuf"]
structure std.path.PathBuf where
  identity : Nat

/-- `Arc<T>` modeled by its contents. Valid only for `T` without interior
    mutability, accessed through shared references (`AsRef`, `Deref`, `Clone`).
    Reference counts, allocation identity (`Arc::ptr_eq`), uniqueness queries
    (`get_mut`, `try_unwrap`, `strong_count`), and drop timing are not modeled;
    model such operations explicitly before relying on them. -/
@[rust_type "alloc::sync::Arc"]
structure alloc.sync.Arc (T : Type _) where
  val : T

/-- A borrowed C string, modeled by its bytes without the trailing NUL. Its
    address is given by the opaque `core.ffi.c_str.CStr.address`. -/
@[rust_type "core::ffi::c_str::CStr"]
structure core.ffi.c_str.CStr where
  bytes : List U8

/-- An owned C string, modeled by its bytes without the trailing NUL.
    Allocation is not modeled. -/
@[rust_type "alloc::ffi::c_str::CString"]
structure alloc.ffi.c_str.CString where
  bytes : List U8

/-- The error of `CString::new` for bytes that contain a NUL. Only the bytes are
    kept; the position of the first NUL is not modeled. -/
@[rust_type "alloc::ffi::c_str::NulError"]
structure alloc.ffi.c_str.NulError where
  bytes : List U8

/-- `LazyLock<T, F>` modeled by its value after initialization. The initializer
    `F`, the time it runs, and synchronization are not modeled. -/
@[rust_type "std::sync::lazy_lock::LazyLock"]
structure std.sync.lazy_lock.LazyLock (T : Type _) (F : Type _) where
  val : T
