import Lake
open Lake DSL

require aeneas from "./aeneas/backends/lean"

package «crosvm-verif» where
  preferReleaseBuild := true

@[default_target]
lean_lib «Resources» where

lean_lib «VmMemory» where

lean_lib «Utils» where

lean_lib «Syscalls» where
