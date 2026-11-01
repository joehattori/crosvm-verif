module
public import VmMemory.GuestMemory.Spec
public import VmMemory.SharedMemory.Spec
public import VmMemory.MemoryMappingBuilder.Spec
public import Utils.Platform
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address
open Syscalls.Memfd

namespace vm_memory.guest_memory.GuestMemory

/-! ### `finalize_shm` -/

/-- The seals `finalize_shm` adds: no shrinking, no growing, and no further
    seals. -/
def finalizeSeals : I32 := F_SEAL_SHRINK ||| F_SEAL_GROW ||| F_SEAL_SEAL

/-- Outcome of `finalize_shm`: add `finalizeSeals` to the shared memory; an
    error becomes `MemoryAddSealsFailed`. -/
def FinalizeShmOutcome (shm : base.shm.SharedMemory)
    (result : core.result.Result Unit vm_memory.guest_memory.Error × base.shm.SharedMemory) :
    Prop :=
  ∃ added, shm.AddSealsOutcome finalizeSeals added ∧ result.2 = added.2 ∧
    result.1 = match added.1 with
      | .Ok () => .Ok ()
      | .Err e => .Err (.MemoryAddSealsFailed e)

@[step]
theorem finalize_shm_spec (shm : base.shm.SharedMemory) :
    sys.linux.finalize_shm shm ⦃ result => FinalizeShmOutcome shm result ⦄ := by
  unfold sys.linux.finalize_shm
  have hseals : ((0#i32 ||| F_SEAL_SHRINK) ||| F_SEAL_GROW) ||| F_SEAL_SEAL = finalizeSeals := by
    rfl
  simp only [base.sys.linux.shm.MemfdSeals.new, base.sys.linux.shm.MemfdSeals.set_shrink_seal,
    base.sys.linux.shm.MemfdSeals.set_grow_seal, base.sys.linux.shm.MemfdSeals.set_seal_seal,
    _root_.libc_1.unix.linux_like.F_SEAL_SHRINK, _root_.libc_1.unix.linux_like.F_SEAL_GROW,
    _root_.libc_1.unix.linux_like.F_SEAL_SEAL, lift, bind_ok]
  rw [show ((0#i32 ||| 0x0002#i32) ||| 0x0004#i32) ||| 0x0001#i32 = finalizeSeals from hseals]
  step as ⟨r, shm1, hadded⟩
  rcases r with _ | e <;>
    simp only [core.result.Result.map_err, bind_ok, bind_tc_ok, WP.spec_ok,
      guest_memory.Error.MemoryAddSealsFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      guest_memory.Error.MemoryAddSealsFailed.constructor] <;>
    exact ⟨_, hadded, rfl, rfl⟩

/-! ### `create_shm` -/

/-- A range passed to `new_with_options`: guest base, size, and options. -/
abbrev Range := GuestAddress × U64 × MemoryRegionOptions

/-- The ranges that the shared memory backs: those without a backing file. -/
def shmRanges (ranges : List Range) : List Range :=
  ranges.filter fun r => r.2.2.file_backed.isNone

/-- A range whose size is a multiple of the page size. -/
def PageAligned (pageSize : Usize) (r : Range) : Prop :=
  r.2.1.val % pageSize.val = 0

instance (pageSize : Usize) (r : Range) : Decidable (PageAligned pageSize r) :=
  inferInstanceAs (Decidable (_ = _))

/-- The sum of the range sizes. -/
def sizeSum (ranges : List Range) : Nat :=
  (ranges.map fun r => r.2.1.val).sum

/-- The sizes that `create_shm` adds with checked addition: those of the
    shared-memory ranges before the first one that isn't page aligned. -/
def shmSizeBeforeUnaligned (pageSize : Usize) (ranges : List Range) : Nat :=
  sizeSum ((shmRanges ranges).takeWhile fun r => decide (PageAligned pageSize r))

/-- The debug name of the guest memory's shared memory. -/
def shmName : List U8 := (toStr "crosvm_guest").val

/-- Create the shared memory of `total` bytes and seal it: a creation error
    becomes `MemoryCreationFailed`, and a sealing error is returned as is. -/
def CreatedShmOutcome (total : U64)
    (result : core.result.Result base.shm.SharedMemory vm_memory.guest_memory.Error) : Prop :=
  ∃ created, base.shm.SharedMemory.NewOutcome shmName total created ∧
    match created with
    | .Err e => result = .Err (.MemoryCreationFailed e)
    | .Ok shm => ∃ finalized, FinalizeShmOutcome shm finalized ∧
      match finalized.1 with
      | .Ok () => result = .Ok finalized.2
      | .Err e => result = .Err e

/-- Outcome of `create_shm`: the first shared-memory range whose size isn't
    page aligned gives `MemoryNotAligned`. Otherwise the shared memory holds
    all shared-memory ranges. -/
def CreateShmOutcome (pageSize : Usize) (ranges : List Range)
    (result : core.result.Result base.shm.SharedMemory vm_memory.guest_memory.Error) : Prop :=
  match (shmRanges ranges).find? fun r => !decide (PageAligned pageSize r) with
  | some r => result = .Err (.MemoryNotAligned r.1 r.2.1)
  | none => ∃ total : U64, total.val = sizeSum (shmRanges ranges) ∧ CreatedShmOutcome total result

private theorem usize_cast_u64_val (x : Usize) : (UScalar.cast .U64 x).val = x.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

private theorem sliceIter_next_of_lt {T : Type} (s : Slice T) (i : Nat)
    (h : i < s.val.length) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (some s.val[i], ⟨s, i + 1⟩) := by
  simp [core.slice.iter.IteratorSliceIter.next, h]
  rfl

private theorem sliceIter_next_of_ge {T : Type} (s : Slice T) (i : Nat)
    (h : s.val.length ≤ i) :
    core.slice.iter.IteratorSliceIter.next ⟨s, i⟩ = ok (none, ⟨s, i⟩) := by
  simp [core.slice.iter.IteratorSliceIter.next, Nat.not_lt.mpr h]

private theorem shmRanges_append (l₁ l₂ : List Range) :
    shmRanges (l₁ ++ l₂) = shmRanges l₁ ++ shmRanges l₂ :=
  List.filter_append _ _

private theorem sizeSum_append (l₁ l₂ : List Range) :
    sizeSum (l₁ ++ l₂) = sizeSum l₁ + sizeSum l₂ := by
  simp [sizeSum]

/-- The part after the loop of `create_shm`. -/
private theorem created_shm_spec (total : U64) :
    (do
      let r ← base.shm.SharedMemory.new
        (core.convert.IntoFrom alloc.vec.VecU8.Insts.CoreConvertFromShared0Str)
        (toStr "crosvm_guest") total
      let r1 ← core.result.Result.map_err
        guest_memory.Error.MemoryCreationFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError
        r guest_memory.Error.MemoryCreationFailed.constructor
      let cf ← core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let (r2, val1) ← sys.linux.finalize_shm val
        let cf1 ← core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch r2
        match cf1 with
        | core.ops.control_flow.ControlFlow.Continue _ =>
          ok (ControlFlow.done (core.result.Result.Ok val1))
        | core.ops.control_flow.ControlFlow.Break residual =>
          let r3 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
            base.shm.SharedMemory (core.convert.FromSame guest_memory.Error) residual
          ok (ControlFlow.done r3)
      | core.ops.control_flow.ControlFlow.Break residual =>
        let r2 ← core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          base.shm.SharedMemory (core.convert.FromSame guest_memory.Error) residual
        ok (ControlFlow.done r2) :
      Result (ControlFlow (core.slice.iter.Iter Range × U64)
        (core.result.Result base.shm.SharedMemory vm_memory.guest_memory.Error)))
    ⦃ cf => ∃ result, cf = .done result ∧ CreatedShmOutcome total result ⦄ := by
  step with base.shm.SharedMemory.new_spec
    (core.convert.IntoFrom alloc.vec.VecU8.Insts.CoreConvertFromShared0Str)
    (toStr "crosvm_guest") { slice := toStr "crosvm_guest" } rfl total as ⟨created, hcreated⟩
  rcases created with shm | e
  · simp only [core.result.Result.map_err_ok, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
    step as ⟨r2, shm1, hfin⟩
    rcases r2 with _ | e
    · simp only [bind_ok,
        WP.spec_ok]
      exact ⟨_, rfl, _, hcreated, _, hfin, rfl⟩
    · simp only [bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
      exact ⟨_, rfl, _, hcreated, _, hfin, rfl⟩
  · simp only [core.result.Result.map_err, bind_ok, bind_tc_ok,
      guest_memory.Error.MemoryCreationFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      guest_memory.Error.MemoryCreationFailed.constructor,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, WP.spec_ok]
    exact ⟨_, rfl, _, hcreated, rfl⟩


/-- The `create_shm` loop at range `k`: the shared-memory ranges before `k` are
    page aligned and their sizes sum to `acc`. It is stated for any loop body
    `F` that runs `create_shm_loop.body`. -/
private theorem create_shm_loop_spec (pageSize : Usize) (hPos : 0 < pageSize.val)
    (s : Slice Range)
    (F : core.slice.iter.Iter Range × U64 →
      Result (ControlFlow (core.slice.iter.Iter Range × U64)
        (core.result.Result base.shm.SharedMemory vm_memory.guest_memory.Error)))
    (hF : ∀ it acc, F (it, acc) = create_shm_loop.body pageSize it acc) :
    ∀ (k : Nat) (acc : U64), k ≤ s.val.length →
      (∀ r ∈ shmRanges (s.val.take k), PageAligned pageSize r) →
      acc.val = sizeSum (shmRanges (s.val.take k)) →
      acc.val + shmSizeBeforeUnaligned pageSize (s.val.drop k) ≤ U64.max →
      loop F (⟨s, k⟩, acc) ⦃ result => CreateShmOutcome pageSize s.val result ⦄ := by
  suffices ∀ n (k : Nat) (acc : U64), s.val.length - k = n → k ≤ s.val.length →
      (∀ r ∈ shmRanges (s.val.take k), PageAligned pageSize r) →
      acc.val = sizeSum (shmRanges (s.val.take k)) →
      acc.val + shmSizeBeforeUnaligned pageSize (s.val.drop k) ≤ U64.max →
      loop F (⟨s, k⟩, acc) ⦃ result => CreateShmOutcome pageSize s.val result ⦄ from
    fun k acc => this _ k acc rfl
  intro n
  induction n with
  | zero =>
    intro k acc hn hk hal hacc _
    have hlen : s.val.length = k := by omega
    have htake : s.val.take k = s.val := List.take_of_length_le (by omega)
    rw [htake] at hal hacc
    rw [loop.eq_def, hF]
    simp only [create_shm_loop.body, sliceIter_next_of_ge s k (by omega), bind_ok, uncurry]
    refine WP.spec_bind (created_shm_spec acc) ?_
    rintro _ ⟨result, rfl, hres⟩
    simp only [WP.spec_ok, CreateShmOutcome]
    rw [List.find?_eq_none.mpr (fun r hr => by simpa using hal r hr)]
    exact ⟨acc, hacc, hres⟩
  | succ n ih =>
    intro k acc hn hk hal hacc hfit
    have hlt : k < s.val.length := by omega
    have hdrop : s.val.drop k = s.val[k] :: s.val.drop (k + 1) := List.drop_eq_getElem_cons hlt
    have htake : s.val.take (k + 1) = s.val.take k ++ [s.val[k]] :=
      List.take_succ_eq_append_getElem hlt
    have hsplit : s.val = s.val.take k ++ s.val[k] :: s.val.drop (k + 1) := by
      rw [← hdrop, List.take_append_drop]
    rw [loop.eq_def, hF]
    simp only [create_shm_loop.body, sliceIter_next_of_lt s k hlt, bind_ok, uncurry]
    rw [hdrop] at hfit
    generalize s.val[k] = r at hfit hsplit htake ⊢
    obtain ⟨ga, size, opts⟩ := r
    simp only [core.option.Option.is_some]
    cases hfb : opts.file_backed with
    | some fb =>
      have hnot : shmRanges [(ga, size, opts)] = [] := by simp [shmRanges, hfb]
      simp only [Option.isSome_some, ↓reduceIte, bind_ok]
      apply ih (k + 1) acc (by omega) (by omega)
      · rw [htake, shmRanges_append, hnot, List.append_nil]
        exact hal
      · rw [htake, shmRanges_append, hnot, List.append_nil]
        exact hacc
      · simpa [shmSizeBeforeUnaligned, shmRanges, hfb] using hfit
    | none =>
      have hyes : shmRanges [(ga, size, opts)] = [(ga, size, opts)] := by simp [shmRanges, hfb]
      simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte, lift, bind_ok]
      have hpage : (UScalar.cast .U64 pageSize).val = pageSize.val := usize_cast_u64_val _
      step as ⟨rem, hrem⟩
      by_cases hal' : PageAligned pageSize (ga, size, opts)
      · have hrem0 : rem = 0#u64 := by
          have hremv : rem.val = 0 := by rw [hrem, hpage]; exact hal'
          exact UScalar.eq_of_val_eq (by simpa using hremv)
        simp only [hrem0, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
        have hsum : acc.val + size.val ≤ U64.max := by
          simp only [shmSizeBeforeUnaligned, shmRanges, List.filter_cons, hfb, Option.isNone_none,
            ↓reduceIte, List.takeWhile_cons, decide_eq_true hal', sizeSum, List.map_cons,
            List.sum_cons] at hfit
          omega
        step as ⟨acc', hacc'⟩
        apply ih (k + 1) acc' (by omega) (by omega)
        · rw [htake, shmRanges_append, hyes]
          intro x hx
          rcases List.mem_append.mp hx with hx | hx
          · exact hal x hx
          · simp only [List.mem_singleton] at hx
            exact hx ▸ hal'
        · rw [htake, shmRanges_append, hyes, sizeSum_append, ← hacc]
          simp [sizeSum, hacc']
        · simp only [shmSizeBeforeUnaligned, shmRanges, List.filter_cons, hfb, Option.isNone_none,
            ↓reduceIte, List.takeWhile_cons, decide_eq_true hal', sizeSum, List.map_cons,
            List.sum_cons] at hfit
          simp only [shmSizeBeforeUnaligned, shmRanges, sizeSum] at ⊢
          omega
      · have hrem0 : rem ≠ 0#u64 := by
          intro h
          apply hal'
          unfold PageAligned
          rw [← hpage, ← hrem, h]
          rfl
        simp only [bne_iff_ne, ne_eq, hrem0, not_false_eq_true, ↓reduceIte, bind_ok, WP.spec_ok]
        simp only [CreateShmOutcome]
        rw [hsplit, shmRanges_append, List.find?_append,
          List.find?_eq_none.mpr (fun x hx => by simpa using hal x hx)]
        simp [shmRanges, hfb, hal']

/-- Verify `GuestMemory::create_shm`, assuming that the page size is positive
    and that the checked sum of the shared-memory sizes doesn't overflow. -/
@[step]
theorem create_shm_spec (ranges : Slice Range) (pageSize : Usize)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPos : 0 < pageSize.val)
    (hFit : shmSizeBeforeUnaligned pageSize ranges.val ≤ U64.max) :
    create_shm ranges ⦃ result => CreateShmOutcome pageSize ranges.val result ⦄ := by
  unfold create_shm
  simp only [hPage, bind_ok,
    SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
  unfold create_shm_loop
  refine create_shm_loop_spec pageSize hPos ranges _ (fun _ _ => rfl) 0 0#u64 (by omega)
    (by simp [shmRanges]) (by simp [shmRanges, sizeSum]) (by simpa using hFit)

/-! ### `new_with_options` -/

@[step]
theorem _root_.vm_memory.guest_memory.MemoryRegionOptions.clone_spec (self : MemoryRegionOptions) :
    MemoryRegionOptions.Insts.CoreCloneClone.clone self ⦃ result => result = self ⦄ := by
  obtain ⟨purpose, align, fb⟩ := self
  cases fb <;>
    simp [MemoryRegionOptions.Insts.CoreCloneClone.clone,
      MemoryRegionPurpose.Insts.CoreCloneClone.clone,
      _root_.core.option.Option.Insts.CoreCloneClone.clone,
      FileBackedMappingParameters.Insts.CoreCloneClone.clone,
      _root_.std.path.PathBuf.Insts.CoreCloneClone.clone, lift,
      core.clone.impls.CloneU64.clone, core.clone.impls.CloneBool.clone]

/-- Whether range `r` starts before the end of the last region of `regions`,
    or the end of that region overflows. -/
def OverlapsLast (regions : List MemoryRegion) (r : Range) : Prop :=
  ∃ prev ∈ regions.getLast?,
    match U64.checked_add prev.guest_base (UScalar.cast .U64 prev.mapping.length) with
    | none => True
    | some prevEnd => r.1.val < prevEnd.val

/-- The protection of a file-backed mapping: read/write when the file is
    writable, read-only otherwise. -/
def fileProtection (fb : FileBackedMappingParameters) : base.mmap.Protection :=
  if fb.writable then { read := true, write := true } else { read := true, write := false }

/-- The region `new_with_options` maps for range `r`, with `shmOffset` bytes of
    the shared memory used before it. A range without a backing file maps the
    shared memory at `shmOffset`. A file-backed range opens its file and maps it
    at the file offset. Mapping errors are wrapped in the matching variant. -/
def RegionOutcome (pageSize : Usize) (shm : alloc.sync.Arc base.shm.SharedMemory)
    (shmOffset : U64) (r : Range)
    (result : core.result.Result MemoryRegion vm_memory.guest_memory.Error) : Prop :=
  match r.2.2.file_backed with
  | none =>
    ∃ builder configured withOffset aligned built,
      base.mmap.MemoryMappingBuilder.NewOutcome (UScalar.cast .Usize r.2.1) builder ∧
      builder.FromSharedMemoryOutcome shm.val configured ∧
      configured.OffsetOutcome shmOffset withOffset ∧
      withOffset.AlignOutcome r.2.2.align aligned ∧
      aligned.BuildOutcome pageSize built ∧
      match built with
      | .Ok mapping => result = .Ok {
          mapping := mapping
          guest_base := r.1
          shared_obj := .Shm shm
          obj_offset := shmOffset
          options := r.2.2 }
      | .Err e => result = .Err (.MemoryMappingFailed e)
  | some fb =>
    match _root_.guest_memory.sys.linux.FileBackedMappingParameters.open_result fb with
    | .Err e => result = .Err (.FiledBackedOpenFailed e)
    | .Ok file =>
      ∃ builder configured withOffset aligned withProtection built,
        base.mmap.MemoryMappingBuilder.NewOutcome (UScalar.cast .Usize r.2.1) builder ∧
        builder.FromFileOutcome file configured ∧
        configured.OffsetOutcome fb.offset withOffset ∧
        withOffset.AlignOutcome r.2.2.align aligned ∧
        aligned.ProtectionOutcome (fileProtection fb) withProtection ∧
        withProtection.BuildOutcome pageSize built ∧
        match built with
        | .Ok mapping => result = .Ok {
            mapping := mapping
            guest_base := r.1
            shared_obj := .File { val := file }
            obj_offset := fb.offset
            options := r.2.2 }
        | .Err e => result = .Err (.FiledBackedMemoryMappingFailed e)

open Classical in
/-- The loop of `new_with_options` over the remaining ranges, after mapping
    `regions` and using `shmOffset` bytes of the shared memory. A range that
    overlaps the last region gives `MemoryRegionOverlap`. Otherwise its region
    is appended, and a range without a backing file uses its size of the shared
    memory. At the end, the regions are accepted in order. -/
def MapRangesOutcome (pageSize : Usize) (shm : alloc.sync.Arc base.shm.SharedMemory) :
    List Range → List MemoryRegion → U64 →
    core.result.Result GuestMemory vm_memory.guest_memory.Error → Prop
  | [], regions, _, result => Accepted regions result
  | r :: rest, regions, shmOffset, result =>
    if OverlapsLast regions r then result = .Err .MemoryRegionOverlap
    else ∃ mapped, RegionOutcome pageSize shm shmOffset r mapped ∧
      match mapped with
      | .Err e => result = .Err e
      | .Ok region => ∃ next : U64, next.val = shmOffset.val + sizeSum (shmRanges [r]) ∧
          MapRangesOutcome pageSize shm rest (regions ++ [region]) next result

/-- Outcome of `GuestMemory::new_with_options`: create the shared memory, then
    map the ranges in order. -/
def NewWithOptionsOutcome (pageSize : Usize) (ranges : List Range)
    (result : core.result.Result GuestMemory vm_memory.guest_memory.Error) : Prop :=
  ∃ created, CreateShmOutcome pageSize ranges created ∧
    match created with
    | .Err e => result = .Err e
    | .Ok shm => MapRangesOutcome pageSize { val := shm } ranges [] 0#u64 result

/-- Every file-backed range has the size of its file parameters. Otherwise
    `new_with_options` panics in `assert_eq!` when it reaches that range. -/
def FileBackedSizesMatch (ranges : List Range) : Prop :=
  ∀ r ∈ ranges, ∀ fb, r.2.2.file_backed = some fb → fb.size = r.2.1


private theorem shm_descriptor_valid (shm : base.shm.SharedMemory) :
    _root_.base.sys.linux.mmap.MemoryMapping.ValidDescriptor
      (Dyn.mk _ base.shm.SharedMemory.Insts.BaseDescriptorAsRawDescriptor shm) :=
  ⟨_, rfl⟩

private theorem file_descriptor_valid (file : _root_.std.fs.File) :
    _root_.base.sys.linux.mmap.MemoryMapping.ValidDescriptor
      (Dyn.mk _ vm_memory.std.fs.File.Insts.BaseDescriptorAsRawDescriptor file) :=
  ⟨_, rfl⟩

/-- The `new_with_options` loop at range `k`. It is stated for any loop body
    `F` that runs `new_with_options_loop.body`. -/
private theorem new_with_options_loop_spec [Platform64] (pageSize : Usize)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo) (hMmap : Syscalls.Mmap.MmapSpec pageSize)
    (hMunmap : Syscalls.Mmap.MunmapSpec) (shm : alloc.sync.Arc base.shm.SharedMemory)
    (s : Slice Range) (hFiles : FileBackedSizesMatch s.val)
    (F : core.slice.iter.Iter Range × alloc.vec.Vec MemoryRegion × U64 →
      Result (ControlFlow (core.slice.iter.Iter Range × alloc.vec.Vec MemoryRegion × U64)
        (core.result.Result GuestMemory vm_memory.guest_memory.Error)))
    (hF : ∀ it regions shmOffset,
      F (it, regions, shmOffset) = new_with_options_loop.body shm it regions shmOffset) :
    ∀ (k : Nat) (regions : alloc.vec.Vec MemoryRegion) (shmOffset : U64),
      k ≤ s.val.length → regions.val.length ≤ k →
      shmOffset.val + sizeSum (shmRanges (s.val.drop k)) ≤ U64.max →
      loop F (⟨s, k⟩, regions, shmOffset) ⦃ result =>
        MapRangesOutcome pageSize shm (s.val.drop k) regions.val shmOffset result ⦄ := by
  suffices ∀ n (k : Nat) (regions : alloc.vec.Vec MemoryRegion) (shmOffset : U64),
      s.val.length - k = n → k ≤ s.val.length → regions.val.length ≤ k →
      shmOffset.val + sizeSum (shmRanges (s.val.drop k)) ≤ U64.max →
      loop F (⟨s, k⟩, regions, shmOffset) ⦃ result =>
        MapRangesOutcome pageSize shm (s.val.drop k) regions.val shmOffset result ⦄ from
    fun k regions shmOffset => this _ k regions shmOffset rfl
  intro n
  induction n with
  | zero =>
    intro k regions shmOffset hn hk _ _
    have hdrop : s.val.drop k = [] := List.drop_eq_nil_of_le (by omega)
    rw [loop.eq_def, hF, hdrop]
    simp only [new_with_options_loop.body, sliceIter_next_of_ge s k (by omega), bind_ok, uncurry,
      alloc.sync.ArcSlice.Insts.CoreConvertFromVec.from, WP.spec_ok, MapRangesOutcome]
    exact ⟨_, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
    intro k regions shmOffset hn hk hlen hfit
    have hlt : k < s.val.length := by omega
    have hdrop : s.val.drop k = s.val[k] :: s.val.drop (k + 1) := List.drop_eq_getElem_cons hlt
    have hmem : s.val[k] ∈ s.val := List.getElem_mem hlt
    have hslen : s.val.length ≤ Usize.max := s.property
    rw [loop.eq_def, hF, hdrop]
    rw [hdrop] at hfit
    simp only [new_with_options_loop.body, sliceIter_next_of_lt s k hlt, bind_ok, uncurry,
      alloc.vec.Vec.deref, _root_.core.slice.Slice.last, Slice.from_val, MapRangesOutcome]
    generalize s.val[k] = r at hfit hmem ⊢
    obtain ⟨ga, size, opts⟩ := r
    have hsizeFit : size.val ≤ Usize.max := Platform64.val_le_usize_max size
    have hsizeCast : (UScalar.cast .Usize size).val = size.val := Platform64.u64_cast_usize_val size
    have htry : ∀ x : U64, Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from x =
        ok (.Ok (UScalar.cast .Usize x)) := by
      intro x
      simp only [Usize.Insts.CoreConvertTryFromU64TryFromIntError.try_from,
        core.num.tryFromUScalar]
      split_ifs with h
      · rfl
      · rw [UScalar.max_USize_eq] at h
        exact absurd (Platform64.val_le_usize_max x) h
    rcases hl : regions.val.getLast? with _ | prev
    on_goal 1 =>
      have hno : ¬ OverlapsLast regions.val (ga, size, opts) := by simp [OverlapsLast, hl]
      simp only [hno, ↓reduceIte]
    on_goal 2 =>
      simp only [base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, lift, bind_ok]
      step as ⟨o2, ho2⟩
      subst ho2
      rcases hc : U64.checked_add prev.guest_base (UScalar.cast .U64 prev.mapping.length)
        with _ | prevEnd
      · have hov : OverlapsLast regions.val (ga, size, opts) := ⟨prev, hl, by simp [hc]⟩
        simp [_root_.core.option.Option.is_none_or, hov]
      simp only [_root_.core.option.Option.is_none_or,
        new_with_options.closure.Insts.CoreOpsFunctionFnOnceTupleGuestAddressBool.call_once]
      step as ⟨b, hb⟩
      by_cases hlt' : ga.val < prevEnd.val
      · have hov : OverlapsLast regions.val (ga, size, opts) := ⟨prev, hl, by simp [hc, hlt']⟩
        have hbt : b = true := hb.mpr hlt'
        simp [hbt, hov]
      have hno : ¬ OverlapsLast regions.val (ga, size, opts) := by
        rintro ⟨p, hp, hpe⟩
        have : p = prev := by simpa [hl] using hp.symm
        subst this
        simp [hc] at hpe
        exact hlt' hpe
      have hbf : b = false := by
        cases b
        · rfl
        · exact absurd (hb.mp rfl) hlt'
      simp only [hbf, Bool.false_eq_true, ↓reduceIte, hno]
    all_goals
      simp only [htry, core.result.Result.map_err_ok, bind_ok,
        core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
      cases hfb : opts.file_backed with
      | none =>
        step as ⟨builder, hbuilder⟩
        step as ⟨configured, hconfigured⟩
        step as ⟨withOffset, hwithOffset⟩
        step as ⟨aligned, haligned⟩
        have hFd : ∀ d, aligned.descriptor = some d →
            _root_.base.sys.linux.mmap.MemoryMapping.ValidDescriptor d := by
          intro d hd
          rw [haligned, hwithOffset, hconfigured] at hd
          simp only [Option.some.injEq] at hd
          subst hd
          exact shm_descriptor_valid _
        step with base.mmap.MemoryMappingBuilder.build_spec aligned pageSize hPage hPagePow hFd
          hMmap hMunmap as ⟨built, hbuilt⟩
        rcases built with mapping | e
        · simp only [core.result.Result.map_err_ok, bind_ok]
          step as ⟨options, hoptions⟩
          subst options
          have hpush : regions.val.length < Usize.max := by omega
          step with alloc.vec.Vec.push_spec regions _ hpush as ⟨regions1, hregions1⟩
          have hcast : (UScalar.cast .U64 (UScalar.cast .Usize size)).val = size.val := by
            rw [usize_cast_u64_val, hsizeCast]
          have hshm : sizeSum (shmRanges ((ga, size, opts) :: s.val.drop (k + 1))) =
              size.val + sizeSum (shmRanges (s.val.drop (k + 1))) := by
            simp [shmRanges, sizeSum, hfb]
          have hadd : shmOffset.val + (UScalar.cast .U64 (UScalar.cast .Usize size)).val ≤
              U64.max := by
            rw [hcast]; omega
          try simp only [lift, bind_ok]
          step as ⟨next, hnext⟩
          have hnextv : next.val = shmOffset.val + size.val := by rw [hnext, hcast]
          refine WP.spec_mono (ih (k + 1) regions1 next (by omega) (by omega)
            (by rw [hregions1]; simp; omega) (by rw [hnextv]; omega)) ?_
          intro result hres
          let region : MemoryRegion := {
            mapping := mapping
            guest_base := ga
            shared_obj := .Shm shm
            obj_offset := shmOffset
            options := opts }
          refine ⟨.Ok region, ?_, next, ?_, ?_⟩
          · simp only [RegionOutcome, hfb]
            exact ⟨builder, configured, withOffset, aligned, _, hbuilder, hconfigured,
              hwithOffset, haligned, hbuilt, rfl⟩
          · rw [hnextv]
            simp [shmRanges, sizeSum, hfb]
          · rw [hregions1] at hres
            exact hres
        · simp only [core.result.Result.map_err, bind_ok, bind_tc_ok,
            guest_memory.Error.MemoryMappingFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
            guest_memory.Error.MemoryMappingFailed.constructor,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, WP.spec_ok]
          refine ⟨.Err _, ?_, rfl⟩
          simp only [RegionOutcome, hfb]
          exact ⟨builder, configured, withOffset, aligned, _, hbuilder, hconfigured,
            hwithOffset, haligned, hbuilt, rfl⟩
      | some fb =>
        have hfbsize : fb.size = size := hFiles _ hmem fb hfb
        simp only [core.result.Result.unwrap, hfbsize, massert, ↓reduceIte, bind_ok]
        cases hopen : _root_.guest_memory.sys.linux.FileBackedMappingParameters.open_result fb with
        | Err e =>
          simp only [core.result.Result.map_err, bind_ok, bind_tc_ok,
            guest_memory.Error.FiledBackedOpenFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
            guest_memory.Error.FiledBackedOpenFailed.constructor,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, WP.spec_ok]
          refine ⟨.Err _, ?_, rfl⟩
          simp only [RegionOutcome, hfb, hopen]
        | Ok file =>
          simp only [core.result.Result.map_err_ok, bind_ok]
          step as ⟨builder, hbuilder⟩
          step as ⟨configured, hconfigured⟩
          step as ⟨withOffset, hwithOffset⟩
          step as ⟨aligned, haligned⟩
          cases hw : fb.writable
          all_goals
            simp only [Bool.false_eq_true, ↓reduceIte]
            step as ⟨p, hp⟩
            step as ⟨withProtection, hwithProtection⟩
            have hprot : p = fileProtection fb := by rw [hp]; simp [fileProtection, hw]
            rw [hprot] at hwithProtection
            have hFd : ∀ d, withProtection.descriptor = some d →
                _root_.base.sys.linux.mmap.MemoryMapping.ValidDescriptor d := by
              intro d hd
              rw [hwithProtection, haligned, hwithOffset, hconfigured] at hd
              simp only [Option.some.injEq] at hd
              subst hd
              exact file_descriptor_valid _
            step with base.mmap.MemoryMappingBuilder.build_spec withProtection pageSize hPage
              hPagePow hFd hMmap hMunmap as ⟨built, hbuilt⟩
            rcases built with mapping | e
            · simp only [core.result.Result.map_err_ok, bind_ok]
              step as ⟨options, hoptions⟩
              subst options
              have hpush : regions.val.length < Usize.max := by omega
              step with alloc.vec.Vec.push_spec regions _ hpush as ⟨regions1, hregions1⟩
              refine WP.spec_mono (ih (k + 1) regions1 shmOffset (by omega) (by omega)
                (by rw [hregions1]; simp; omega)
                (by simpa [shmRanges, sizeSum, hfb] using hfit)) ?_
              intro result hres
              let region : MemoryRegion := {
                mapping := mapping
                guest_base := ga
                shared_obj := .File { val := file }
                obj_offset := fb.offset
                options := opts }
              refine ⟨.Ok region, ?_, shmOffset, ?_, ?_⟩
              · simp only [RegionOutcome, hfb, hopen]
                exact ⟨builder, configured, withOffset, aligned, withProtection, _, hbuilder,
                  hconfigured, hwithOffset, haligned, hwithProtection, hbuilt, rfl⟩
              · simp [shmRanges, sizeSum, hfb]
              · rw [hregions1] at hres
                exact hres
            · simp only [core.result.Result.map_err, bind_ok, bind_tc_ok,
                guest_memory.Error.FiledBackedMemoryMappingFailed.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
                guest_memory.Error.FiledBackedMemoryMappingFailed.constructor,
                core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                core.convert.FromSame.from, WP.spec_ok]
              refine ⟨.Err _, ?_, rfl⟩
              simp only [RegionOutcome, hfb, hopen]
              exact ⟨builder, configured, withOffset, aligned, withProtection, _, hbuilder,
                hconfigured, hwithOffset, haligned, hwithProtection, hbuilt, rfl⟩


/-- Verify `GuestMemory::new_with_options`, assuming the `mmap(2)`/`munmap(2)`
    contracts, that the checked sum of the shared-memory sizes doesn't
    overflow, and that every file-backed range matches its file size. -/
@[step]
theorem new_with_options_spec (ranges : Slice Range) (pageSize : Usize) [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo) (hMmap : Syscalls.Mmap.MmapSpec pageSize)
    (hMunmap : Syscalls.Mmap.MunmapSpec)
    (hFit : shmSizeBeforeUnaligned pageSize ranges.val ≤ U64.max)
    (hFiles : FileBackedSizesMatch ranges.val) :
    new_with_options ranges ⦃ result => NewWithOptionsOutcome pageSize ranges.val result ⦄ := by
  have hPos : 0 < pageSize.val := Nat.pos_of_isPowerOfTwo hPagePow
  unfold new_with_options
  step with create_shm_spec ranges pageSize hPage hPos hFit as ⟨created, hcreated⟩
  rcases created with shm | e
  · simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok,
      SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
    have hsum : sizeSum (shmRanges ranges.val) ≤ U64.max := by
      simp only [CreateShmOutcome] at hcreated
      split at hcreated
      · simp at hcreated
      · rename_i hnone
        have hall := List.find?_eq_none.mp hnone
        have htw : (shmRanges ranges.val).takeWhile (fun r => decide (PageAligned pageSize r)) =
            shmRanges ranges.val := by
          have h := List.takeWhile_append_of_pos (l₂ := [])
            (p := fun r => decide (PageAligned pageSize r)) (fun x hx => by simpa using hall x hx)
          simpa using h
        simpa [shmSizeBeforeUnaligned, htw] using hFit
    refine WP.spec_mono (P₀ := MapRangesOutcome pageSize { val := shm } ranges.val [] 0#u64) ?_
      (fun result h => ⟨_, hcreated, h⟩)
    unfold new_with_options_loop
    refine WP.spec_mono (new_with_options_loop_spec pageSize hPage hPagePow hMmap hMunmap
      { val := shm } ranges hFiles _ ?_ 0 (alloc.vec.Vec.new MemoryRegion) 0#u64 (by omega)
      (by simp) (by simpa using hsum)) ?_
    · intro _ _ _
      rfl
    · intro result h
      simpa using h
  · simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      core.convert.FromSame.from, bind_tc_ok, WP.spec_ok]
    exact ⟨_, hcreated, rfl⟩

end vm_memory.guest_memory.GuestMemory
