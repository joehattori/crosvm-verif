module
public import VmMemory.Types
public import Utils.CoreExternal
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory

/-- Null mutable raw pointer at address 0. -/
@[reducible, rust_fun "core::ptr::null_mut"]
def core.ptr.null_mut (T : Type _) : Result (MutRawPtr T) :=
  ok { addr := 0#usize }

/-- Whether a mutable raw pointer's address is 0. -/
@[reducible, rust_fun "core::ptr::mut_ptr::{*mut @T}::is_null"]
def core.ptr.mut_ptr.RawPtrMutT.is_null {T : Type _} (self : MutRawPtr T) : Result Bool :=
  ok (self.addr == 0#usize)

/-- Byte-offset wrapping pointer addition (used on `*mut c_void`, where pointee size is 1). -/
@[reducible, rust_fun "core::ptr::mut_ptr::{*mut @T}::wrapping_add"]
def core.ptr.mut_ptr.RawPtrMutT.wrapping_add {T : Type _}
    (self : MutRawPtr T) (count : Std.Usize) : Result (MutRawPtr T) :=
  ok { addr := core.num.Usize.wrapping_add self.addr count }

/-- `Option::default` returns `None`. -/
@[reducible, rust_fun
  "core::option::{core::default::Default<core::option::Option<@T>>}::default"]
def core.option.Option.Insts.CoreDefaultDefault.default (T : Type _) : Result (Option T) :=
  ok none

/-- Shared access to the `Arc` contents; the allocator parameter is ignored. -/
@[reducible, rust_fun
  "alloc::sync::{core::convert::AsRef<alloc::sync::Arc<@T>, @T>}::as_ref"]
def alloc.sync.Arc.Insts.CoreConvertAsRef.as_ref {T : Type _} (_A : Type _)
    (self : alloc.sync.Arc T) : Result T :=
  ok self.val

/-- Shared dereference of the `Arc` contents; the allocator parameter is ignored. -/
@[reducible, rust_fun
  "alloc::sync::{core::ops::deref::Deref<alloc::sync::Arc<@T>, @T>}::deref"]
def alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref {T : Type _} (_A : Type _)
    (self : alloc.sync.Arc T) : Result T :=
  ok self.val

/-- Short-circuiting `Iterator::any` for slice iterators: call the predicate on
    each remaining element in order, stop after the first accepted element, and
    return the advanced iterator. Predicate state is threaded between calls. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::any"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.any
    {T F : Type _} (fnMutInst : core.ops.function.FnMut F T Bool)
    (it : core.slice.iter.Iter T) (f : F) : Result (Bool × core.slice.iter.Iter T) :=
  if h : it.i < it.slice.val.length then do
    let call ← fnMutInst.call_mut f it.slice.val[it.i]
    if call.1 then ok (true, { it with i := it.i + 1 })
    else any fnMutInst { it with i := it.i + 1 } call.2
  else ok (false, it)
termination_by it.slice.val.length - it.i

/-- `Iterator::find` for slice iterators: call the predicate on each remaining
    element in order, and return the first accepted element together with the
    iterator advanced past it. Predicate state is threaded between calls. -/
@[rust_fun
  "core::slice::iter::{core::iter::traits::iterator::Iterator<core::slice::iter::Iter<'a, @T>, &'a @T>}::find"]
def core.slice.iter.Iter.Insts.CoreIterTraitsIteratorIteratorSharedAT.find
    {T P : Type _} (fnMutInst : core.ops.function.FnMut P T Bool)
    (it : core.slice.iter.Iter T) (predicate : P) :
    Result (Option T × core.slice.iter.Iter T) :=
  if h : it.i < it.slice.val.length then do
    let call ← fnMutInst.call_mut predicate it.slice.val[it.i]
    if call.1 then ok (some it.slice.val[it.i], { it with i := it.i + 1 })
    else find fnMutInst { it with i := it.i + 1 } call.2
  else ok (none, it)
termination_by it.slice.val.length - it.i

/-- Keep the larger of `best` and each remaining item, comparing their keys
    with `Ord::cmp`. As in Rust's `cmp::max_by`, a later item replaces `best`
    unless `best`'s key is strictly greater, so ties select the last item. A
    non-terminating iterator may diverge. -/
def core.iter.traits.iterator.Iterator.maxByKeyFrom {Self B F Item : Type _}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item) (ordInst : core.cmp.Ord B)
    (fInst : core.ops.function.FnMut F Item B) (best : B × Item) (iter : Self) (f : F) :
    Result (Option Item) := do
  let step ← iteratorInst.next iter
  match step.1 with
  | none => ok (some best.2)
  | some x =>
    let call ← fInst.call_mut f x
    let order ← ordInst.cmp best.1 call.1
    let best := if order = .gt then best else (call.1, x)
    maxByKeyFrom iteratorInst ordInst fInst best step.2 call.2
partial_fixpoint

/-- Rust's default `Iterator::max_by_key`: compute each item's key once, in
    order, and return the last item with a maximal key, or `None` for an empty
    iterator. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::max_by_key"]
def core.iter.traits.iterator.Iterator.max_by_key.default {Self B F Item : Type _}
    (iteratorInst : core.iter.traits.iterator.Iterator Self Item) (ordInst : core.cmp.Ord B)
    (fInst : core.ops.function.FnMut F Item B) (self : Self) (f : F) :
    Result (Option Item) := do
  let step ← iteratorInst.next self
  match step.1 with
  | none => ok none
  | some x =>
    let call ← fInst.call_mut f x
    core.iter.traits.iterator.Iterator.maxByKeyFrom iteratorInst ordInst fInst
      (call.1, x) step.2 call.2

/-- `Option::map_or` applies the closure to a present value and returns
    `default` otherwise. -/
@[rust_fun "core::option::{core::option::Option<@T>}::map_or"]
def core.option.Option.map_or {T U F : Type _} (fnInst : core.ops.function.FnOnce F T U)
    (self : Option T) (default : U) (f : F) : Result U :=
  match self with
  | none => ok default
  | some x => fnInst.call_once f x

/-- `Iterator::sum` delegates to the `Sum` implementation of the result type. -/
@[trait_default, rust_fun "core::iter::traits::iterator::Iterator::sum"]
def core.iter.traits.iterator.Iterator.sum.default {Self S Clause0_Item : Type _}
    (IteratorInst : core.iter.traits.iterator.Iterator Self Clause0_Item)
    (accumSumInst : core.iter.traits.accum.Sum S Clause0_Item) (self : Self) : Result S :=
  accumSumInst.sum IteratorInst self

/-- Add the remaining items to `acc` in order. The standard library inherits the
    caller's overflow checks for this addition, and crosvm builds with
    `overflow-checks = true`, so an overflowing partial sum fails. A
    non-terminating iterator may diverge. -/
def U64.Insts.CoreIterTraitsAccumSumU64.sumFrom {I : Type _}
    (iteratorInst : core.iter.traits.iterator.Iterator I U64) (acc : U64) (iter : I) :
    Result U64 := do
  let step ← iteratorInst.next iter
  match step.1 with
  | none => ok acc
  | some x =>
    let acc ← acc + x
    sumFrom iteratorInst acc step.2
partial_fixpoint

/-- `u64: Sum<u64>` folds the iterator from zero with checked addition. -/
@[rust_fun "core::iter::traits::accum::{core::iter::traits::accum::Sum<u64, u64>}::sum"]
def U64.Insts.CoreIterTraitsAccumSumU64.sum {I : Type _}
    (iteratorIteratorIU64Inst : core.iter.traits.iterator.Iterator I U64) (iter : I) :
    Result U64 :=
  sumFrom iteratorIteratorIU64Inst 0#u64 iter
@[rust_fun
  "base::sys::unix::descriptor::{base::descriptor::AsRawDescriptor<std::fs::File>}::as_raw_descriptor"]
def std.fs.File.Insts.BaseDescriptorAsRawDescriptor.as_raw_descriptor
    (self : std.fs.File) : Result I32 :=
  ok self.descriptor

/-- Logical length of the platform mapping carried by the translated wrapper. -/
abbrev vm_memory.base.mmap.MemoryMapping.length
    (self : vm_memory.base.mmap.MemoryMapping) : Usize := self.mapping.size

/-- Model the stable length returned by MappedRegion::size. -/
@[rust_fun "base::mmap::{base::mmap::MappedRegion<base::mmap::MemoryMapping>}::size"]
def base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size
    (self : vm_memory.base.mmap.MemoryMapping) : Result Usize :=
  ok self.length

/-- Descriptor cloning is outside the verified wrap(_, None) path used by build.
    No behavior or normal termination is assumed for this opaque operation. -/
@[rust_fun
  "base::descriptor::{core::convert::TryFrom<base::descriptor::SafeDescriptor, &'0 @, core::io::error::Error>}::try_from"]
opaque base.descriptor.SafeDescriptor.Insts.CoreConvertTryFromShared0PError.try_from
    (descriptor : Dyn vm_memory.base.descriptor.AsRawDescriptor) :
    Result (core.result.Result vm_memory.base.descriptor.SafeDescriptor core.io.error.Error) :=
  fail .panic

/-- Opaque host errno value returned by `base::errno::Error::last`. -/
opaque base.errno.Error.last_errno : base.errno.Error := { errno := 0#i32 }

/-- Host errno lookup after a failed system call. -/
@[rust_fun "base::errno::{base::errno::Error}::last"]
def base.errno.Error.last : Result base.errno.Error :=
  ok base.errno.Error.last_errno

/-- Opaque host page size. Proofs assume an explicit successful return and do
    not rely on the witness value. -/
@[rust_fun "base::sys::unix::system_info::pagesize"]
opaque vm_memory.base.sys.unix.system_info.pagesize : Result Std.Usize := ok 4096#usize

@[reducible, rust_const "libc#1::unix::linux_like::PROT_READ"]
def libc_1.unix.linux_like.PROT_READ : Result Std.I32 := ok 0x0001#i32

@[reducible, rust_const "libc#1::unix::linux_like::PROT_WRITE"]
def libc_1.unix.linux_like.PROT_WRITE : Result Std.I32 := ok 0x0002#i32

@[reducible, rust_const "libc#1::unix::linux_like::MAP_SHARED"]
def libc_1.unix.linux_like.MAP_SHARED : Result Std.I32 := ok 0x0001#i32

@[reducible, rust_const "libc#1::unix::linux_like::MAP_PRIVATE"]
def libc_1.unix.linux_like.MAP_PRIVATE : Result Std.I32 := ok 0x0002#i32

@[reducible, rust_const "libc#1::unix::linux_like::MAP_FIXED"]
def libc_1.unix.linux_like.MAP_FIXED : Result Std.I32 := ok 0x0010#i32

@[reducible, rust_const "libc#1::unix::linux_like::linux::gnu::b64::x86_64::MAP_ANONYMOUS"]
def libc_1.unix.linux_like.linux.gnu.b64.x86_64.MAP_ANONYMOUS : Result Std.I32 := ok 0x0020#i32

@[reducible, rust_const "libc#1::unix::linux_like::linux::gnu::b64::x86_64::MAP_NORESERVE"]
def libc_1.unix.linux_like.linux.gnu.b64.x86_64.MAP_NORESERVE : Result Std.I32 := ok 0x4000#i32

@[reducible, rust_const "libc#1::unix::linux_like::linux::gnu::b64::x86_64::MAP_POPULATE"]
def libc_1.unix.linux_like.linux.gnu.b64.x86_64.MAP_POPULATE : Result Std.I32 := ok 0x8000#i32

/-- Sentinel returned by `mmap64` on failure (`!0usize as *mut c_void`). -/
@[reducible, rust_const "libc#1::unix::linux_like::MAP_FAILED"]
def libc_1.unix.linux_like.MAP_FAILED : Result (MutRawPtr core.ffi.c_void) :=
  ok { addr := core.num.Usize.MAX }

@[reducible, rust_const "libc#1::unix::linux_like::F_GET_SEALS"]
def libc_1.unix.linux_like.F_GET_SEALS : Result Std.I32 := ok 1034#i32

@[reducible, rust_const "libc#1::unix::linux_like::F_SEAL_WRITE"]
def libc_1.unix.linux_like.F_SEAL_WRITE : Result Std.I32 := ok 0x0008#i32

@[reducible, rust_const "libc#1::unix::linux_like::MADV_MERGEABLE"]
def libc_1.unix.linux_like.MADV_MERGEABLE : Result Std.I32 := ok 12#i32

@[reducible, rust_const "libc#1::unix::linux_like::MADV_DONTDUMP"]
def libc_1.unix.linux_like.MADV_DONTDUMP : Result Std.I32 := ok 16#i32

/-- Opaque external model of `libc::mmap64`. Specifications constrain the
    returned pointer on success and `MAP_FAILED` on failure. -/
@[rust_fun "libc#1::unix::linux_like::mmap64"]
opaque libc_1.unix.linux_like.mmap64
    (addr : MutRawPtr core.ffi.c_void) (size : Std.Usize)
    (prot flags fd : Std.I32) (offset : Std.I64) :
    Result (MutRawPtr core.ffi.c_void) :=
  fail .panic

/-- Opaque external model of `libc::munmap`. Specifications constrain the
    permitted unmap regions and their outcomes. -/
@[rust_fun "libc#1::unix::munmap"]
opaque libc_1.unix.munmap
    (addr : MutRawPtr core.ffi.c_void) (len : Std.Usize) : Result Std.I32 :=
  fail .panic

/-- Opaque return value of `libc::fcntl`. -/
opaque libc_1.unix.fcntl_status (fd cmd : Std.I32) : Std.I32 := (-1)#i32

/-- External model of `libc::fcntl` returning the opaque C status/seals value. -/
@[reducible, rust_fun "libc#1::unix::fcntl"]
def libc_1.unix.fcntl (fd cmd : Std.I32) : Result Std.I32 :=
  ok (libc_1.unix.fcntl_status fd cmd)

/-- Opaque return code of `libc::madvise`. -/
opaque libc_1.unix.linux_like.linux_l4re_shared.madvise_status
    (addr : MutRawPtr core.ffi.c_void) (len : Std.Usize) (advice : Std.I32) :
    Std.I32 := 0#i32

/-- External model of `libc::madvise` returning the opaque C status code. -/
@[reducible, rust_fun "libc#1::unix::linux_like::linux_l4re_shared::madvise"]
def libc_1.unix.linux_like.linux_l4re_shared.madvise
    (addr : MutRawPtr core.ffi.c_void) (len : Std.Usize) (advice : Std.I32) :
    Result Std.I32 :=
  ok (libc_1.unix.linux_like.linux_l4re_shared.madvise_status addr len advice)
