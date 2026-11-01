module
public import VmMemory.FunsExternal
@[expose] public section
open Aeneas Aeneas.Std Result

/-! Flag constants for `memfd_create(2)` and the `fcntl(2)` seal commands.
    The system calls themselves are modeled in `VmMemory/FunsExternal.lean` by
    opaque return values, so they need no contract here. -/

namespace Syscalls.Memfd

/-- Set the close-on-exec flag on the new descriptor (`0x0001`). -/
abbrev MFD_CLOEXEC : U32 := 0x0001#u32

/-- Allow seals to be added to the file (`0x0002`). -/
abbrev MFD_ALLOW_SEALING : U32 := 0x0002#u32

/-- Make the file non-executable and seal its mode (`0x0008`). -/
abbrev MFD_NOEXEC_SEAL : U32 := 0x0008#u32

/-- Invalid argument (`EINVAL`). -/
abbrev EINVAL : I32 := 22#i32

end Syscalls.Memfd
