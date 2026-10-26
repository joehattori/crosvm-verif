module
public import VmMemory.MemoryMapping.Spec
@[expose] public section
open Aeneas Aeneas.Std Result
open _root_.base.sys.linux.mmap (MappingBacking)
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

/-- Linux selects provenance from the descriptor, independently of the file flag.
    An offset is used only for descriptor-backed mappings. -/
def expectedBacking (self : MemoryMappingBuilder) : MappingBacking :=
  match self.descriptor with
  | none => .anonymous
  | some descriptor => .descriptor (descriptor_backing descriptor) (self.offset.getD 0#u64)

/-- The observed response of the selected lower operation, with exactly the
    arguments supplied by build. Early rejection requires no external response. -/
def BuildResponse (self : MemoryMappingBuilder) (status : core.result.Result Unit Error) : Prop :=
  match self.descriptor with
  | none =>
    if self.populate then status = .Err .InvalidArgument
    else new_protection_status self.size self.align self.effectiveProtection = ok status
  | some descriptor =>
    from_fd_offset_protection_populate_status descriptor self.size
      (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate = ok status

/-- The wrap(_, None) operation used on both successful build paths preserves
    the platform mapping and does not retain a cloned descriptor. -/
def WrapOutcome (mapping : _root_.base.sys.linux.mmap.MemoryMapping)
    (result : core.result.Result MemoryMapping Error) : Prop :=
  result = .Ok { mapping := mapping, _file_descriptor := none }

/-- Compose the creation metadata/error contract with wrapping or unchanged
    error propagation. Early rejection is represented by its Rust error. -/
def BuildOutcome (self : MemoryMappingBuilder) (status : core.result.Result Unit Error)
    (result : core.result.Result MemoryMapping Error) : Prop :=
  ∃ created, CreationOutcome self.size self.expectedBacking self.effectiveProtection status created ∧
    match created with
    | .Ok mapping => WrapOutcome mapping result
    | .Err error => result = .Err error

/-- Successful builds retain all creation metadata through the Rust wrapper. -/
theorem BuildOutcome.success {self : MemoryMappingBuilder}
    {status : core.result.Result Unit Error} {mapping : MemoryMapping}
    (h : BuildOutcome self status (.Ok mapping)) :
    mapping.length = self.size ∧ mapping.mapping.backing = self.expectedBacking ∧
      mapping.mapping.readable = self.effectiveProtection.read ∧
      mapping.mapping.writable = self.effectiveProtection.write ∧
      mapping._file_descriptor = none := by
  obtain ⟨created, hc, hw⟩ := h
  cases created with
  | Err error => simp at hw
  | Ok inner =>
    have heq : mapping = { mapping := inner, _file_descriptor := none } := by
      simpa [WrapOutcome] using hw
    subst mapping
    obtain ⟨hl, hb, hr, hw⟩ := hc.success
    exact ⟨hl, hb, hr, hw, rfl⟩

/-- Every successful build has the requested length, regardless of its status witness. -/
theorem BuildOutcome.length_eq {self : MemoryMappingBuilder}
    {status : core.result.Result Unit Error} {mapping : MemoryMapping}
    (h : BuildOutcome self status (.Ok mapping)) :
    mapping.length = self.size := h.success.1

theorem BuildOutcome.backing_eq {self : MemoryMappingBuilder}
    {status : core.result.Result Unit Error} {mapping : MemoryMapping}
    (h : BuildOutcome self status (.Ok mapping)) :
    mapping.mapping.backing = self.expectedBacking := h.success.2.1

theorem BuildOutcome.error {self : MemoryMappingBuilder} {error : Error}
    {result : core.result.Result MemoryMapping Error}
    (h : BuildOutcome self (.Err error) result) : result = .Err error := by
  obtain ⟨created, hc, hw⟩ := h
  rwa [hc.error] at hw

theorem BuildOutcome.ok {self : MemoryMappingBuilder}
    {result : core.result.Result MemoryMapping Error}
    (h : BuildOutcome self (.Ok ()) result) : ∃ mapping, result = .Ok mapping := by
  obtain ⟨created, hc, hw⟩ := h
  obtain ⟨mapping, rfl, _⟩ := hc
  exact ⟨_, hw⟩

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
theorem wrap_none_spec (mapping : _root_.base.sys.linux.mmap.MemoryMapping) :
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

/-- Verify Rust's dispatch, defaults, wrapping, and error propagation using the
    selected lower operation's external creation contract. -/
@[step]
theorem build_spec (self : MemoryMappingBuilder) (status : core.result.Result Unit Error)
    (hResponse : BuildResponse self status) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result =>
      BuildOutcome self status result ⦄ := by
  unfold base.sys.linux.mmap.MemoryMappingBuilder.build
  cases hd : self.descriptor with
  | none =>
    cases hp : self.populate with
    | true =>
      have hs : status = .Err .InvalidArgument := by
        simpa [BuildResponse, hd, hp] using hResponse
      subst status
      simp only [↓reduceIte, WP.spec_ok]
      exact ⟨.Err .InvalidArgument, rfl, rfl⟩
    | false =>
      have hs : new_protection_status self.size self.align self.effectiveProtection = ok status := by
        simpa [BuildResponse, hd, hp] using hResponse
      simp only [Bool.false_eq_true, ↓reduceIte]
      simp only [effective_protection_eq, bind_ok]
      step with new_protection_spec self.size self.align self.effectiveProtection status hs as ⟨created, hc⟩
      have hc' : CreationOutcome self.size self.expectedBacking self.effectiveProtection status created := by
        simpa [expectedBacking, hd] using hc
      cases created with
      | Ok mapping =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with wrap_none_spec mapping as ⟨result, hr⟩
        exact ⟨.Ok mapping, hc', hr⟩
      | Err error =>
        simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
        step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
          MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
        exact ⟨.Err error, hc', hr⟩
  | some descriptor =>
    have hs := hResponse
    simp only [BuildResponse, hd] at hs
    simp only [unwrap_or_eq_getD, lift, bind_ok]
    simp only [effective_protection_eq, bind_ok]
    step with from_fd_offset_protection_populate_spec descriptor self.size
      (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate
      status hs as ⟨created, hc⟩
    have hc' : CreationOutcome self.size self.expectedBacking self.effectiveProtection status created := by
      simpa [expectedBacking, hd] using hc
    cases created with
    | Ok mapping =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with wrap_none_spec mapping as ⟨result, hr⟩
      exact ⟨.Ok mapping, hc', hr⟩
    | Err error =>
      simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch, bind_ok]
      step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
        MemoryMapping (core.convert.FromSame Error) error error rfl as ⟨result, hr⟩
      exact ⟨.Err error, hc', hr⟩

/-- Anonymous population is rejected before any external operation is called. -/
theorem build_populate_invalid_spec (self : MemoryMappingBuilder)
    (hDescriptor : self.descriptor = none) (hPopulate : self.populate = true) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result =>
      result = .Err .InvalidArgument ⦄ := by
  simp [base.sys.linux.mmap.MemoryMappingBuilder.build, hDescriptor, hPopulate]

/-- A returned Rust error stays a normal return with the same error value. -/
theorem build_error_spec (self : MemoryMappingBuilder) (error : Error)
    (hResponse : BuildResponse self (.Err error)) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self ⦃ result => result = .Err error ⦄ := by
  step with build_spec self (.Err error) hResponse as ⟨result, hr⟩
  exact hr.error

/-- A failure of the selected anonymous creation operation propagates through build. -/
theorem build_anonymous_failure (self : MemoryMappingBuilder) (error : Aeneas.Std.Error)
    (hDescriptor : self.descriptor = none) (hPopulate : self.populate = false)
    (hStatus : new_protection_status self.size self.align self.effectiveProtection = fail error) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self = fail error := by
  have hf := new_protection_failure self.size self.align self.effectiveProtection error hStatus
  simp [base.sys.linux.mmap.MemoryMappingBuilder.build, hDescriptor, hPopulate,
    effective_protection_eq, hf]

/-- A failure of the selected descriptor-backed creation operation also propagates. -/
theorem build_descriptor_failure (self : MemoryMappingBuilder)
    (descriptor : Dyn base.descriptor.AsRawDescriptor) (error : Aeneas.Std.Error)
    (hDescriptor : self.descriptor = some descriptor)
    (hStatus : from_fd_offset_protection_populate_status descriptor self.size
      (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate = fail error) :
    base.sys.linux.mmap.MemoryMappingBuilder.build self = fail error := by
  have hf := from_fd_offset_protection_populate_failure descriptor self.size
    (self.offset.getD 0#u64) (self.align.getD 0#u64) self.effectiveProtection self.populate error hStatus
  simp [base.sys.linux.mmap.MemoryMappingBuilder.build, hDescriptor, unwrap_or_eq_getD,
    effective_protection_eq, lift, hf]

end vm_memory.base.mmap.MemoryMappingBuilder
