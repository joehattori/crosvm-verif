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

/-- Outcome of `MemoryMappingBuilder::build`, dispatching to `NewProtectionOutcome`
    for anonymous mappings and `FromFdOutcome` for descriptor-backed mappings, and
    wrapping any created `PlatformMemoryMapping` with `WrapOutcome`. Anonymous
    population is rejected before any system call. -/
def BuildOutcome (self : MemoryMappingBuilder) (pageSize : Usize)
    (result : core.result.Result MemoryMapping Error) : Prop :=
  match self.descriptor with
  | none =>
    if self.populate then result = .Err .InvalidArgument
    else
      ∃ created,
        NewProtectionOutcome pageSize self.size self.align self.effectiveProtection created ∧
        match created with
        | .Ok mapping => WrapOutcome mapping result
        | .Err error => result = .Err error
  | some descriptor =>
    ∃ created,
      FromFdOutcome pageSize descriptor self.size
        (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate created ∧
      match created with
      | .Ok mapping => WrapOutcome mapping result
      | .Err error => result = .Err error

/-- Properties guaranteed by `BuildOutcome` whenever a build succeeds with `.Ok mapping`:
    the mapping has the requested length and `_file_descriptor = none`, the mapped
    address is not `MAP_FAILED`, the mapped region `[addr, addr + size)` fits in the
    user address space without wrapping, and the address satisfies the requested or
    page alignment. -/
theorem BuildOutcome.mapped_properties {self : MemoryMappingBuilder}
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
  cases hd : self.descriptor with
  | none =>
    simp only [BuildOutcome, hd] at hOut
    split at hOut
    · simp at hOut
    · obtain ⟨created, hc, hw⟩ := hOut
      cases created with
      | Err error => simp at hw
      | Ok inner =>
        have heq : mapping = { mapping := inner, _file_descriptor := none } := by
          simpa [WrapOutcome] using hw
        subst mapping
        obtain ⟨hsize, hne, hfit, _, hpage, halign⟩ := hc.mapped_properties
        refine ⟨hsize, rfl, hne, hfit, fun _ ha => hpage rfl ha, ?_⟩
        rintro a hpos (⟨_, ha⟩ | ⟨hsome, _⟩)
        · exact halign a rfl ha hpos
        · simp at hsome
  | some descriptor =>
    simp only [BuildOutcome, hd] at hOut
    obtain ⟨created, hc, hw⟩ := hOut
    cases created with
    | Err error => simp at hw
    | Ok inner =>
      have heq : mapping = { mapping := inner, _file_descriptor := none } := by
        simpa [WrapOutcome] using hw
      subst mapping
      obtain ⟨hsize, hne, hfit, _, _, halign⟩ := hc.mapped_properties
      refine ⟨hsize, rfl, hne, hfit, by simp, ?_⟩
      rintro a hpos (⟨hnone, _⟩ | ⟨_, ha⟩)
      · simp at hnone
      · subst ha
        exact halign (self.align.getD 0#u64) rfl rfl hpos

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
theorem build_spec (self : MemoryMappingBuilder) (pageSize : Usize)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hAlign : AlignSizeFits pageSize self.size self.align)
    (hFd : ∀ d, self.descriptor = some d → ValidDescriptor d)
    (hMmap : MmapSpec pageSize)
    (hMunmap : MunmapSpec
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
        hPage hAlign hMmap hMunmap as ⟨created, hc⟩
      cases created with
      | Ok mapping =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with wrap_none_spec mapping as ⟨result, hr⟩
        simp only [BuildOutcome, hd, hp, Bool.false_eq_true, ↓reduceIte]
        exact ⟨.Ok mapping, hc, hr⟩
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
          MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
        simp only [BuildOutcome, hd, hp, Bool.false_eq_true, ↓reduceIte]
        exact ⟨.Err error, hc, hr⟩
  | some descriptor =>
    simp only [unwrap_or_eq_getD, lift, bind_ok]
    simp only [effective_protection_eq, bind_ok]
    step with from_fd_offset_protection_populate_spec pageSize descriptor self.size
      (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate
      hPage hAlign.of_getD_zero (hFd descriptor hd) hMmap (MunmapSpec.of_getD_zero hMunmap) as ⟨created, hc⟩
    cases created with
    | Ok mapping =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with wrap_none_spec mapping as ⟨result, hr⟩
      simp only [BuildOutcome, hd]
      exact ⟨.Ok mapping, hc, hr⟩
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
        MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
      simp only [BuildOutcome, hd]
      exact ⟨.Err error, hc, hr⟩

/-- Anonymous population is rejected before any external operation is called. -/
theorem build_populate_invalid_spec (self : MemoryMappingBuilder)
    (hDescriptor : self.descriptor = none) (hPopulate : self.populate = true) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result =>
      result = .Err .InvalidArgument ⦄ := by
  simp [base.sys.linux.mmap.MemoryMappingBuilder.build, hDescriptor, hPopulate]

end vm_memory.base.mmap.MemoryMappingBuilder
