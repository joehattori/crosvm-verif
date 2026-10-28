module
public import VmMemory.GuestAddress.Spec
public import VmMemory.MemoryMappingBuilder.Spec
@[expose] public section
open Aeneas Aeneas.Std Result
open vm_memory.guest_address
open Syscalls.Mmap
open _root_.base.sys.linux.mmap.MemoryMapping

namespace vm_memory.guest_memory.MemoryRegionOptions

/-- The derived default: general-purpose guest memory, no alignment, and no
    file-backed mapping parameters. -/
def defaultOptions : MemoryRegionOptions :=
  { purpose := .GuestMemoryRegion, align := 0#u64, file_backed := none }

@[step]
theorem default_spec :
    MemoryRegionOptions.Insts.CoreDefaultDefault.default ⦃ o => o = defaultOptions ⦄ := by
  simp [MemoryRegionOptions.Insts.CoreDefaultDefault.default,
    MemoryRegionPurpose.Insts.CoreDefaultDefault.default, defaultOptions]
  rfl

end vm_memory.guest_memory.MemoryRegionOptions

namespace vm_memory.guest_memory.MemoryRegion

/-- The exclusive end of a region is representable as a guest address. -/
def ValidBounds (self : MemoryRegion) : Prop :=
  self.guest_base.val + self.mapping.length.val ≤ U64.max

/-- Region `self` ends at or before region `other` starts, so their half-open
    guest ranges are disjoint and `self` starts no later than `other`. -/
def EndsBefore (self other : MemoryRegion) : Prop :=
  self.guest_base.val + self.mapping.length.val ≤ other.guest_base.val

/-- The exact endpoint computed by Rust's unchecked_add, including wraparound. -/
def EndOutcome (self : MemoryRegion) (result : GuestAddress) : Prop :=
  result = U64.wrapping_add self.guest_base (UScalar.cast .U64 self.mapping.length)

theorem EndOutcome.exists (self : MemoryRegion) :
    ∃ result, EndOutcome self result :=
  ⟨_, rfl⟩

private theorem length_cast_val (length : Usize) :
    (UScalar.cast .U64 length).val = length.val := by
  apply UScalar.cast_val_mod_pow_greater_numBits_eq
  cases System.Platform.numBits_eq <;> simp_all [UScalarTy.numBits]

/-- Under valid bounds, the wrapping endpoint is the mathematical exclusive end. -/
theorem EndOutcome.val_eq_of_valid {self : MemoryRegion} {result : GuestAddress}
    (he : EndOutcome self result) (h : ValidBounds self) :
    result.val = self.guest_base.val + self.mapping.length.val := by
  rw [he, U64.wrapping_add_val_eq, length_cast_val]
  apply Nat.mod_eq_of_lt
  unfold ValidBounds at h
  scalar_tac

@[step]
theorem start_spec (self : MemoryRegion) :
    self.start ⦃ r => r = self.guest_base ⦄ := by
  simp [MemoryRegion.start]

/-- Exact behavior even when the exclusive end wraps around the address space. -/
@[step]
theorem end_spec (self : MemoryRegion) :
    self.end ⦃ r => EndOutcome self r ⦄ := by
  unfold MemoryRegion.end
  simp only [base.mmap.MemoryMapping.Insts.BaseMmapMappedRegion.size, bind_ok, lift]
  step as ⟨r, hr⟩
  exact hr

/-- The end is exclusive; the bound excludes a mathematical end of 2^64. -/
theorem end_no_overflow_spec (self : MemoryRegion) (h : ValidBounds self) :
    self.end ⦃ r => r.val = self.guest_base.val + self.mapping.length.val ⦄ := by
  step as ⟨r, hr⟩
  exact hr.val_eq_of_valid h

/-- Membership uses the endpoint specified by EndOutcome, even if it wraps. -/
def ContainsOutcome (self : MemoryRegion) (addr : GuestAddress) (b : Bool) : Prop :=
  ∃ endAddr, EndOutcome self endAddr ∧
    (b = true ↔ self.guest_base.val ≤ addr.val ∧ addr.val < endAddr.val)

/-- `ContainsOutcome` determines the result: it holds for `b` exactly when `b`
    agrees with whether it holds for `true`. -/
theorem ContainsOutcome.eq_true_iff {self : MemoryRegion} {addr : GuestAddress} {b : Bool}
    (h : self.ContainsOutcome addr b) : b = true ↔ self.ContainsOutcome addr true := by
  obtain ⟨endAddr, he, hb⟩ := h
  constructor
  · intro hbt
    exact ⟨endAddr, he, by simp [← hb, hbt]⟩
  · rintro ⟨endAddr', he', hb'⟩
    have : endAddr' = endAddr := he'.trans he.symm
    subst this
    exact hb.mpr (hb'.mp rfl)

@[step]
theorem contains_spec (self : MemoryRegion) (addr : GuestAddress) :
    self.contains addr ⦃ b => self.ContainsOutcome addr b ⦄ := by
  unfold MemoryRegion.contains
  step as ⟨b, hb⟩
  split
  · step as ⟨endAddr, he⟩
    step as ⟨result, hr⟩
    refine ⟨endAddr, he, ?_⟩
    simp_all
  · obtain ⟨endAddr, he⟩ := EndOutcome.exists self
    simp only [WP.spec_ok]
    refine ⟨endAddr, he, ?_⟩
    simp_all

/-- Checked-add overflow returns false; otherwise compare the checked request
    end with the region endpoint specified by EndOutcome. -/
@[step]
theorem contains_range_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64) :
    self.contains_range addr size ⦃ b =>
      match U64.checked_add addr size with
      | none => b = false
      | some endAddr =>
        ∃ regionEnd, EndOutcome self regionEnd ∧
          (b = true ↔ self.guest_base.val ≤ addr.val ∧
            endAddr.val ≤ regionEnd.val) ⦄ := by
  unfold MemoryRegion.contains_range
  step as ⟨o, ho⟩
  rw [← ho]
  cases o with
  | none => simp
  | some endAddr =>
    step as ⟨b, hb⟩
    split
    · step as ⟨regionEnd, he⟩
      step as ⟨result, hr⟩
      refine ⟨regionEnd, he, ?_⟩
      simp_all
    · obtain ⟨regionEnd, he⟩ := EndOutcome.exists self
      simp only [WP.spec_ok]
      refine ⟨regionEnd, he, ?_⟩
      simp_all

/-- Valid bounds recover membership in the mathematical half-open interval. -/
theorem contains_no_overflow_spec (self : MemoryRegion) (addr : GuestAddress)
    (h : ValidBounds self) :
    self.contains addr ⦃ b =>
      b = true ↔ self.guest_base.val ≤ addr.val ∧
        addr.val < self.guest_base.val + self.mapping.length.val ⦄ := by
  apply WP.spec_mono (contains_spec self addr)
  rintro b ⟨endAddr, he, hb⟩
  rwa [he.val_eq_of_valid h] at hb

/-- Valid bounds recover mathematical containment, including empty requests. -/
theorem contains_range_no_overflow_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64)
    (h : ValidBounds self) :
    self.contains_range addr size ⦃ b =>
      b = true ↔ self.guest_base.val ≤ addr.val ∧
        addr.val + size.val ≤ self.guest_base.val + self.mapping.length.val ⦄ := by
  apply WP.spec_mono (contains_range_spec self addr size)
  intro b hb
  have hAdd := U64.checked_add_bv_spec addr size
  cases ho : U64.checked_add addr size with
  | none =>
    simp only [ho] at hb hAdd
    simp only [hb, Bool.false_eq_true, false_iff, not_and]
    intro _ hFit
    exact Nat.not_le_of_gt hAdd (hFit.trans h)
  | some endAddr =>
    simp only [ho] at hb hAdd
    obtain ⟨regionEnd, he, hb⟩ := hb
    rwa [he.val_eq_of_valid h, hAdd.2.1] at hb

/-- Zero-length regions contain no individual address, including their start. -/
theorem contains_empty_spec (self : MemoryRegion) (addr : GuestAddress)
    (hEmpty : self.mapping.length.val = 0) :
    self.contains addr ⦃ b => b = false ⦄ := by
  have h : ValidBounds self := by
    simp only [ValidBounds, hEmpty, Nat.add_zero]
    scalar_tac
  apply WP.spec_mono (contains_no_overflow_spec self addr h)
  intro b hb
  simp [hEmpty] at hb
  cases b <;> simp_all
  omega

/-- An empty request at the exclusive end is accepted, even for an empty region. -/
theorem contains_range_empty_at_end_spec (self : MemoryRegion) (addr : GuestAddress)
    (h : ValidBounds self)
    (hEnd : addr.val = self.guest_base.val + self.mapping.length.val) :
    self.contains_range addr 0#u64 ⦃ b => b = true ⦄ := by
  apply WP.spec_mono (contains_range_no_overflow_spec self addr 0#u64 h)
  intro b hb
  apply hb.mpr
  simp [hEnd]

/-- Query overflow returns false regardless of the region's own bounds. -/
theorem contains_range_overflow_spec (self : MemoryRegion) (addr : GuestAddress) (size : U64)
    (hOverflow : U64.max < addr.val + size.val) :
    self.contains_range addr size ⦃ b => b = false ⦄ := by
  apply WP.spec_mono (contains_range_spec self addr size)
  intro b hb
  have hAdd := U64.checked_add_bv_spec addr size
  cases ho : U64.checked_add addr size with
  | none => simpa only [ho] using hb
  | some endAddr =>
    simp only [ho] at hAdd
    omega

/-- Region constructors wrap the built mapping: on success, store it with the
    guest base, backing object, offset, and default options; on failure, wrap
    the mapping error in `MemoryMappingFailed`. -/
def MappedRegionOutcome (built : core.result.Result base.mmap.MemoryMapping base.mmap.Error)
    (guest_base : GuestAddress) (shared_obj : BackingObject) (offset : U64)
    (result : core.result.Result MemoryRegion guest_memory.Error) : Prop :=
  match built with
  | .Ok mapping =>
    result = .Ok {
      mapping := mapping
      guest_base := guest_base
      shared_obj := shared_obj
      obj_offset := offset
      options := MemoryRegionOptions.defaultOptions }
  | .Err error => result = .Err (.MemoryMappingFailed error)

/-- The shared tail of `new_from_shm` and `new_from_file` after `build`. -/
private theorem mapped_region_spec
    (built : core.result.Result base.mmap.MemoryMapping base.mmap.Error)
    (guest_base : GuestAddress) (shared_obj : BackingObject) (offset : U64) :
    (do
      let r1 ← core.result.Result.map_err P.Insts.CoreOpsFunctionFnOnceTupleErrorError built
        guest_memory.Error.MemoryMappingFailed.constructor
      let cf ← core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch r1
      match cf with
      | core.ops.control_flow.ControlFlow.Continue val =>
        let mro ← MemoryRegionOptions.Insts.CoreDefaultDefault.default
        ok (core.result.Result.Ok
          ({
            mapping := val,
            guest_base := guest_base,
            shared_obj := shared_obj,
            obj_offset := offset,
            options := mro
          } : MemoryRegion))
      | core.ops.control_flow.ControlFlow.Break residual =>
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
          MemoryRegion (core.convert.FromSame guest_memory.Error) residual)
    ⦃ result => MappedRegionOutcome built guest_base shared_obj offset result ⦄ := by
  cases built with
  | Ok mapping =>
    simp only [core.result.Result.map_err_ok, bind_ok,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
    step as ⟨options, hOpt⟩
    simp [MappedRegionOutcome, hOpt]
  | Err error =>
    simp only [core.result.Result.map_err_err,
      P.Insts.CoreOpsFunctionFnOnceTupleErrorError.call_once,
      guest_memory.Error.MemoryMappingFailed.constructor,
      core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
    step with core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual_Err.spec
      MemoryRegion (core.convert.FromSame guest_memory.Error) _ _ rfl as ⟨result, hr⟩
    exact hr

/-- A successfully built region stores the given fields and inherits the
    length, descriptor, and address-space fit of the mapping built from `builder`. -/
theorem MappedRegionOutcome.ok_properties {builder : base.mmap.MemoryMappingBuilder}
    {pageSize : Usize} {built : core.result.Result base.mmap.MemoryMapping base.mmap.Error}
    {guest_base : GuestAddress} {shared_obj : BackingObject} {offset : U64}
    {region : MemoryRegion}
    (hBuilt : builder.BuildOutcome pageSize built)
    (h : MappedRegionOutcome built guest_base shared_obj offset (.Ok region)) :
    region.guest_base = guest_base ∧
    region.shared_obj = shared_obj ∧
    region.obj_offset = offset ∧
    region.options = MemoryRegionOptions.defaultOptions ∧
    region.mapping.length = builder.size ∧
    region.mapping._file_descriptor = none ∧
    region.mapping.mapping.addr.addr.val + region.mapping.length.val ≤ Usize.max := by
  cases built with
  | Err error => simp [MappedRegionOutcome] at h
  | Ok mapping =>
    simp only [MappedRegionOutcome, core.result.Result.Ok.injEq] at h
    subst h
    obtain ⟨hlen, hfd, _, hfit, _⟩ := hBuilt.mapped_properties
    exact ⟨rfl, rfl, rfl, rfl, hlen, hfd, hlen ▸ hfit⟩

/-- Every failure is a `MemoryMappingFailed` error. -/
theorem MappedRegionOutcome.err
    {built : core.result.Result base.mmap.MemoryMapping base.mmap.Error}
    {guest_base : GuestAddress} {shared_obj : BackingObject} {offset : U64}
    {error : guest_memory.Error}
    (h : MappedRegionOutcome built guest_base shared_obj offset (.Err error)) :
    ∃ mmapError, error = .MemoryMappingFailed mmapError := by
  cases built with
  | Ok mapping => simp [MappedRegionOutcome] at h
  | Err mmapError => exact ⟨mmapError, by simpa [MappedRegionOutcome] using h⟩

private theorem cast_usize_val_of_le (size : U64) (hSize : size.val ≤ Usize.max) :
    (UScalar.cast .Usize size).val = size.val := by
  rw [UScalar.cast_val_eq]
  apply Nat.mod_eq_of_lt
  scalar_tac

/-! ### `new_from_shm` -/

/-- Outcome of `MemoryRegion::new_from_shm`: configure a builder for `size as usize`
    bytes of the shared memory at `offset`, build it, and wrap the result with
    the `Arc` backing object. -/
def NewFromShmOutcome (pageSize : Usize) (size : U64) (guest_base : GuestAddress)
    (offset : U64) (shm : alloc.sync.Arc base.shm.SharedMemory)
    (result : core.result.Result MemoryRegion guest_memory.Error) : Prop :=
  ∃ builder configured withOffset built,
    base.mmap.MemoryMappingBuilder.NewOutcome (UScalar.cast .Usize size) builder ∧
    builder.FromSharedMemoryOutcome shm.val configured ∧
    configured.OffsetOutcome offset withOffset ∧
    withOffset.BuildOutcome pageSize built ∧
    MappedRegionOutcome built guest_base (.Shm shm) offset result

/-- Verify `MemoryRegion::new_from_shm`: assuming the host page size and
    `MmapSpec`, the result satisfies `NewFromShmOutcome`. No alignment is
    requested, so no trimming `munmap` call is permitted and `MunmapSpec` holds
    vacuously. -/
@[step]
theorem new_from_shm_spec (size : U64) (guest_base : GuestAddress) (offset : U64)
    (shm : alloc.sync.Arc base.shm.SharedMemory) (pageSize : Usize)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hMmap : MmapSpec pageSize) :
    new_from_shm size guest_base offset shm ⦃ result =>
      NewFromShmOutcome pageSize size guest_base offset shm result ⦄ := by
  unfold new_from_shm
  simp only [lift, bind_ok, alloc.sync.Arc.Insts.CoreConvertAsRef.as_ref]
  step as ⟨builder, hNew⟩
  step as ⟨configured, hConf⟩
  step as ⟨withOffset, hOff⟩
  have hDesc : withOffset.descriptor =
      some (Dyn.mk _ base.shm.SharedMemory.Insts.BaseDescriptorAsRawDescriptor shm.val) := by
    rw [show withOffset = _ from hOff, show configured = _ from hConf]
  have hNone : withOffset.align = none := by
    rw [show withOffset = _ from hOff, show configured = _ from hConf,
      show builder = _ from hNew]
  step with base.mmap.MemoryMappingBuilder.build_spec withOffset pageSize hPage
    (hNone ▸ AlignSizeFits.of_none _ _)
    (by rw [hDesc]; rintro d ⟨⟩; exact ⟨_, rfl⟩) hMmap (hNone ▸ MunmapSpec.of_none _ _ _)
    as ⟨built, hBuilt⟩
  apply WP.spec_mono (mapped_region_spec built guest_base (.Shm shm) offset)
  intro result hr
  exact ⟨builder, configured, withOffset, built, hNew, hConf, hOff, hBuilt, hr⟩

/-- Properties of a region created by `new_from_shm`: it stores the requested
    guest base, backing object, offset, and default options; its mapping has
    length `size as usize`, retains no duplicated descriptor, and fits in the
    address space without wrapping. -/
theorem NewFromShmOutcome.ok_properties {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {shm : alloc.sync.Arc base.shm.SharedMemory}
    {region : MemoryRegion}
    (h : NewFromShmOutcome pageSize size guest_base offset shm (.Ok region)) :
    region.guest_base = guest_base ∧
    region.shared_obj = .Shm shm ∧
    region.obj_offset = offset ∧
    region.options = MemoryRegionOptions.defaultOptions ∧
    region.mapping.length = UScalar.cast .Usize size ∧
    region.mapping._file_descriptor = none ∧
    region.mapping.mapping.addr.addr.val + region.mapping.length.val ≤ Usize.max := by
  obtain ⟨builder, configured, withOffset, built, hNew, hConf, hOff, hBuilt, hr⟩ := h
  subst hNew hConf hOff
  exact MappedRegionOutcome.ok_properties hBuilt hr

/-- When `size` fits in `usize` (always on 64-bit targets), the mapping length
    equals the requested size. -/
theorem NewFromShmOutcome.length_val {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {shm : alloc.sync.Arc base.shm.SharedMemory}
    {region : MemoryRegion}
    (h : NewFromShmOutcome pageSize size guest_base offset shm (.Ok region))
    (hSize : size.val ≤ Usize.max) :
    region.mapping.length.val = size.val := by
  rw [h.ok_properties.2.2.2.2.1, cast_usize_val_of_le size hSize]

/-- Every failure of `new_from_shm` is a `MemoryMappingFailed` error. -/
theorem NewFromShmOutcome.err {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {shm : alloc.sync.Arc base.shm.SharedMemory}
    {error : guest_memory.Error}
    (h : NewFromShmOutcome pageSize size guest_base offset shm (.Err error)) :
    ∃ mmapError, error = .MemoryMappingFailed mmapError := by
  obtain ⟨_, _, _, _, _, _, _, _, hr⟩ := h
  exact hr.err

/-! ### `new_from_file` -/

/-- Outcome of `MemoryRegion::new_from_file`: configure a builder for
    `size as usize` bytes of the file at `offset`, build it, and wrap the result
    with the `Arc` backing object. -/
def NewFromFileOutcome (pageSize : Usize) (size : U64) (guest_base : GuestAddress)
    (offset : U64) (file : alloc.sync.Arc std.fs.File)
    (result : core.result.Result MemoryRegion guest_memory.Error) : Prop :=
  ∃ builder configured withOffset built,
    base.mmap.MemoryMappingBuilder.NewOutcome (UScalar.cast .Usize size) builder ∧
    builder.FromFileOutcome file.val configured ∧
    configured.OffsetOutcome offset withOffset ∧
    withOffset.BuildOutcome pageSize built ∧
    MappedRegionOutcome built guest_base (.File file) offset result

/-- Verify `MemoryRegion::new_from_file`: assuming the host page size and
    `MmapSpec`, the result satisfies `NewFromFileOutcome`. No alignment is
    requested, so no trimming `munmap` call is permitted and `MunmapSpec` holds
    vacuously. -/
@[step]
theorem new_from_file_spec (size : U64) (guest_base : GuestAddress) (offset : U64)
    (file : alloc.sync.Arc std.fs.File) (pageSize : Usize)
    (hPage : vm_memory.base.sys.unix.system_info.pagesize = ok pageSize)
    (hMmap : MmapSpec pageSize) :
    new_from_file size guest_base offset file ⦃ result =>
      NewFromFileOutcome pageSize size guest_base offset file result ⦄ := by
  unfold new_from_file
  simp only [lift, bind_ok, alloc.sync.Arc.Insts.CoreOpsDerefDeref.deref]
  step as ⟨builder, hNew⟩
  step as ⟨configured, hConf⟩
  step as ⟨withOffset, hOff⟩
  have hDesc : withOffset.descriptor =
      some (Dyn.mk _ std.fs.File.Insts.BaseDescriptorAsRawDescriptor file.val) := by
    rw [show withOffset = _ from hOff, show configured = _ from hConf]
  have hNone : withOffset.align = none := by
    rw [show withOffset = _ from hOff, show configured = _ from hConf,
      show builder = _ from hNew]
  step with base.mmap.MemoryMappingBuilder.build_spec withOffset pageSize hPage
    (hNone ▸ AlignSizeFits.of_none _ _)
    (by rw [hDesc]; rintro d ⟨⟩; exact ⟨_, rfl⟩) hMmap (hNone ▸ MunmapSpec.of_none _ _ _)
    as ⟨built, hBuilt⟩
  apply WP.spec_mono (mapped_region_spec built guest_base (.File file) offset)
  intro result hr
  exact ⟨builder, configured, withOffset, built, hNew, hConf, hOff, hBuilt, hr⟩

/-- Properties of a region created by `new_from_file`: it stores the requested
    guest base, backing object, offset, and default options; its mapping has
    length `size as usize`, retains no duplicated descriptor, and fits in the
    address space without wrapping. -/
theorem NewFromFileOutcome.ok_properties {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {file : alloc.sync.Arc std.fs.File}
    {region : MemoryRegion}
    (h : NewFromFileOutcome pageSize size guest_base offset file (.Ok region)) :
    region.guest_base = guest_base ∧
    region.shared_obj = .File file ∧
    region.obj_offset = offset ∧
    region.options = MemoryRegionOptions.defaultOptions ∧
    region.mapping.length = UScalar.cast .Usize size ∧
    region.mapping._file_descriptor = none ∧
    region.mapping.mapping.addr.addr.val + region.mapping.length.val ≤ Usize.max := by
  obtain ⟨builder, configured, withOffset, built, hNew, hConf, hOff, hBuilt, hr⟩ := h
  subst hNew hConf hOff
  exact MappedRegionOutcome.ok_properties hBuilt hr

/-- When `size` fits in `usize` (always on 64-bit targets), the mapping length
    equals the requested size. -/
theorem NewFromFileOutcome.length_val {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {file : alloc.sync.Arc std.fs.File}
    {region : MemoryRegion}
    (h : NewFromFileOutcome pageSize size guest_base offset file (.Ok region))
    (hSize : size.val ≤ Usize.max) :
    region.mapping.length.val = size.val := by
  rw [h.ok_properties.2.2.2.2.1, cast_usize_val_of_le size hSize]

/-- Every failure of `new_from_file` is a `MemoryMappingFailed` error. -/
theorem NewFromFileOutcome.err {pageSize : Usize} {size : U64}
    {guest_base : GuestAddress} {offset : U64} {file : alloc.sync.Arc std.fs.File}
    {error : guest_memory.Error}
    (h : NewFromFileOutcome pageSize size guest_base offset file (.Err error)) :
    ∃ mmapError, error = .MemoryMappingFailed mmapError := by
  obtain ⟨_, _, _, _, _, _, _, _, hr⟩ := h
  exact hr.err

end vm_memory.guest_memory.MemoryRegion
