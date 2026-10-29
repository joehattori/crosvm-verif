module
public import VmMemory.MemoryMapping.Spec
@[expose] public section
open Aeneas Aeneas.Std Result
open Syscalls.Mmap
open _root_.base.sys.linux.mmap.MemoryMapping

namespace vm_memory.base.mmap.MemoryMappingBuilder

/-- Initial configuration: the requested size and no optional settings. -/
def NewOutcome (size : Usize) (result : MemoryMappingBuilder) : Prop :=
  result = {
    descriptor := none
    is_file_descriptor := false
    size := size
    offset := none
    align := none
    protection := none
    populate := false
  }

/-- Select the supplied file and set the file flag, preserving every other field. -/
def FromFileOutcome (self : MemoryMappingBuilder) (file : _root_.std.fs.File)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with
    descriptor := some (Dyn.mk _ vm_memory.std.fs.File.Insts.BaseDescriptorAsRawDescriptor file)
    is_file_descriptor := true }

/-- Select the supplied shared memory, preserving every other field, including
    the existing file flag. -/
def FromSharedMemoryOutcome (self : MemoryMappingBuilder) (shm : base.shm.SharedMemory)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with
    descriptor := some (Dyn.mk _ base.shm.SharedMemory.Insts.BaseDescriptorAsRawDescriptor shm) }

/-- Set the explicit offset, preserving every other field. No validation occurs. -/
def OffsetOutcome (self : MemoryMappingBuilder) (offset : U64)
    (result : MemoryMappingBuilder) : Prop :=
  result = { self with offset := some offset }

/-- The default access requested by build is read/write. -/
def effectiveProtection (self : MemoryMappingBuilder) : Protection :=
  self.protection.getD { read := true, write := true }

/-- The wrap(_, None) operation used on both successful build paths preserves
    the platform mapping and does not retain a cloned descriptor. -/
def WrapOutcome (mapping : PlatformMemoryMapping)
    (result : core.result.Result MemoryMapping Error) : Prop :=
  result = .Ok { mapping := mapping, _file_descriptor := none }

/-- Building an anonymous populated mapping is rejected. Otherwise successful
    builds satisfy the mapping contract and retain no cloned descriptor.
    Other ordinary Rust errors are unconstrained. -/
def BuildOutcome (self : MemoryMappingBuilder) (pageSize : Usize)
    (result : core.result.Result MemoryMapping Error) : Prop :=
  if self.descriptor.isNone && self.populate then result = .Err .InvalidArgument
  else
    match result with
    | .Ok mapping =>
      mapping._file_descriptor = none ∧
      MappingProperties pageSize none self.size self.align mapping.mapping
    | .Err _ => True

/-- Properties guaranteed by `BuildOutcome` whenever a build succeeds with `.Ok mapping`:
    the mapping has the requested length and `_file_descriptor = none`, the mapped
    address is not `MAP_FAILED`, the mapped region `[addr, addr + size)` fits in `usize`
    without wrapping, and the address satisfies the requested or
    page alignment. -/
theorem BuildOutcome.mapped_properties [Platform64] {self : MemoryMappingBuilder}
    {pageSize : Usize} {mapping : MemoryMapping}
    (hOut : BuildOutcome self pageSize (.Ok mapping)) :
    mapping.length = self.size ∧
    mapping._file_descriptor = none ∧
    mapping.mapping.addr.addr ≠ core.num.Usize.MAX ∧
    mapping.mapping.addr.addr.val + self.size.val ≤ Usize.max ∧
    (self.descriptor = none → self.align = none →
      mapping.mapping.addr.addr.val % pageSize.val = 0) ∧
    (∀ a, 0 < a.val →
      (self.descriptor = none ∧ self.align = some a ∨
        self.descriptor.isSome ∧ self.align.getD 0#u64 = a) →
      mapping.mapping.addr.addr.val % a.val = 0) := by
  unfold BuildOutcome at hOut
  split at hOut
  · simp at hOut
  · obtain ⟨hfd, h⟩ := hOut
    refine ⟨h.size_eq, hfd, h.not_map_failed, h.range_fits, ?_, ?_⟩
    · intro _ _
      exact h.page_aligned
    · rintro a hpos (⟨_, ha⟩ | ⟨_, ha⟩)
      · have hrequested := h.requested_alignment
        rw [ha] at hrequested
        exact (hrequested hpos).2
      · cases halign : self.align with
        | none => simp [halign] at ha; subst a; simp at hpos
        | some b =>
          have hab : b = a := by simpa [halign] using ha
          have hrequested := h.requested_alignment
          rw [halign, hab] at hrequested
          exact (hrequested hpos).2

/-- Every successful build is page aligned, regardless of its requested alignment. -/
theorem BuildOutcome.page_aligned {self : MemoryMappingBuilder}
    {pageSize : Usize} {mapping : MemoryMapping}
    (hOut : BuildOutcome self pageSize (.Ok mapping)) :
    mapping.mapping.addr.addr.val % pageSize.val = 0 := by
  unfold BuildOutcome at hOut
  split at hOut
  · simp at hOut
  · exact hOut.2.page_aligned

@[step]
theorem new_spec (size : Usize) :
    MemoryMappingBuilder.new size ⦃ result => NewOutcome size result ⦄ := by
  simp [MemoryMappingBuilder.new, NewOutcome]

@[step]
theorem from_file_spec (self : MemoryMappingBuilder) (file : _root_.std.fs.File) :
    self.from_file file ⦃ result => FromFileOutcome self file result ⦄ := by
  simp [MemoryMappingBuilder.from_file, FromFileOutcome]

@[step]
theorem from_shared_memory_spec (self : MemoryMappingBuilder) (shm : base.shm.SharedMemory) :
    self.from_shared_memory shm ⦃ result => FromSharedMemoryOutcome self shm result ⦄ := by
  simp [MemoryMappingBuilder.from_shared_memory, FromSharedMemoryOutcome]

@[step]
theorem offset_spec (self : MemoryMappingBuilder) (offset : U64) :
    impl.offset self offset ⦃ result => OffsetOutcome self offset result ⦄ := by
  simp [impl.offset, OffsetOutcome]

@[step]
theorem wrap_none_spec (mapping : PlatformMemoryMapping) :
    base.sys.linux.mmap.MemoryMappingBuilder.wrap mapping none ⦃ result =>
      WrapOutcome mapping result ⦄ := by
  simp [base.sys.linux.mmap.MemoryMappingBuilder.wrap, WrapOutcome]

private theorem effective_protection_eq (self : MemoryMappingBuilder) :
    core.option.Option.unwrap_or_else P.Insts.CoreOpsFunctionFnOnceTupleProtection
      self.protection Protection.read_write = ok self.effectiveProtection := by
  cases hp : self.protection <;>
    simp [core.option.Option.unwrap_or_else, hp, effectiveProtection,
      P.Insts.CoreOpsFunctionFnOnceTupleProtection.call_once, Protection.read_write]

private theorem unwrap_or_eq_getD {T : Type} (value : Option T) (fallback : T) :
    core.option.Option.unwrap_or value fallback = value.getD fallback := by
  cases value <;> rfl

/-- Verify `MemoryMappingBuilder::build`: assuming `MmapSpec pageSize` and
    `MunmapSpec`, `build` satisfies `BuildOutcome`. -/
@[step]
theorem build_spec (self : MemoryMappingBuilder) (pageSize : Usize) [Platform64]
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hPagePow : pageSize.val.isPowerOfTwo)
    (hFd : ∀ d, self.descriptor = some d → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec pageSize
      (TryMmapTrimAllowed pageSize self.size self.align
        (protectionFlags self.effectiveProtection))) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result =>
      BuildOutcome self pageSize result ⦄ := by
  unfold base.sys.linux.mmap.MemoryMappingBuilder.build
  cases hd : self.descriptor with
  | none =>
    cases hp : self.populate with
    | true =>
      simp [BuildOutcome, hd, hp]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [effective_protection_eq, bind_ok]
      step with new_protection_spec pageSize self.size self.align self.effectiveProtection
        hPage hPagePow hMmap hMunmap as ⟨created, hc⟩
      cases created with
      | Ok mapping =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with wrap_none_spec mapping as ⟨result, hr⟩
        change result = .Ok { mapping := mapping, _file_descriptor := none } at hr
        subst result
        simpa [BuildOutcome, hd, hp, MappingResultProperties] using hc
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
          MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
        simp [BuildOutcome, hd, hp, hr]
  | some descriptor =>
    simp only [unwrap_or_eq_getD, lift, bind_ok]
    simp only [effective_protection_eq, bind_ok]
    step with from_fd_offset_protection_populate_spec pageSize descriptor self.size
      (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate
      hPage hPagePow (hFd descriptor hd) hMmap (MunmapSpec.of_getD_zero hMunmap) as ⟨created, hc⟩
    cases created with
    | Ok mapping =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with wrap_none_spec mapping as ⟨result, hr⟩
      change result = .Ok { mapping := mapping, _file_descriptor := none } at hr
      subst result
      have hprops := MappingProperties.of_getD_zero hc
      simpa [BuildOutcome, hd] using hprops
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
        MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
      simp [BuildOutcome, hd, hr]

/-- Anonymous population is rejected before any external operation is called. -/
theorem build_populate_invalid_spec (self : MemoryMappingBuilder)
    (hDescriptor : self.descriptor = none) (hPopulate : self.populate = true) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result =>
      result = .Err .InvalidArgument ⦄ := by
  simp [base.sys.linux.mmap.MemoryMappingBuilder.build, hDescriptor, hPopulate]

end vm_memory.base.mmap.MemoryMappingBuilder
