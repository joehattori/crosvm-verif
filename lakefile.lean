import Lake
open Lake DSL

require aeneas from "./aeneas/backends/lean"

package «crosvm-verif» where
  preferReleaseBuild := true

@[default_target]
lean_lib «CrosvmVerif» where

lean_lib «Resources» where
  roots := #[]
  globs := #[.submodules `Resources]

lean_lib «VmMemory» where
  roots := #[]
  globs := #[.submodules `VmMemory]

lean_lib «Utils» where
  roots := #[]
  globs := #[.submodules `Utils]

lean_lib «Syscalls» where
  roots := #[]
  globs := #[.submodules `Syscalls]
