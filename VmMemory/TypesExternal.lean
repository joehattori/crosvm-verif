module
public import Aeneas
@[expose] public section
open Aeneas Aeneas.Std

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
structure alloc.sync.Arc (T : Type) where
  val : T
