module
public import Resources.AddressAllocator.Spec
public import Resources.AddressAllocatorSet.Spec
import all Resources.FunsExternal
import all Aeneas.Std.Slice
import all Aeneas.Std.SliceIter
import all Aeneas.Std.VecIter
import all Aeneas.Std.Scalar.Ops.Add
import all Aeneas.Std.String
import all Init.Data.ByteArray.Basic
@[expose] public section
open Aeneas Aeneas.Std Result
set_option maxHeartbeats 1000000
open resources.address_range resources.address_allocator resources.system_allocator

namespace resources.system_allocator.SystemAllocator

@[simp] private theorem val_max (x y : U64) : (max x y).val = max x.val y.val := by
  simp only [max_def]
  split_ifs <;> scalar_tac

@[simp] private theorem val_min (x y : U64) : (min x y).val = min x.val y.val := by
  simp only [min_def]
  split_ifs <;> scalar_tac

/-- Inclusive intersection, including its empty endpoint representation. -/
def intersection (r s : AddressRange) : AddressRange :=
  ⟨max r.start s.start, min r.end s.end⟩

/-- An empty restriction list leaves the original pool unrestricted. -/
def mmioPools (ranges : List AddressRange) (pool : AddressRange) : List AddressRange :=
  if ranges = [] then [pool] else ranges.map (fun r => intersection r pool)

private theorem intersect_eq_spec (r s : AddressRange) :
    AddressRange.intersect r s ⦃ result => result = intersection r s ⦄ := by
  unfold AddressRange.intersect
  step
  step
  simp_all [intersection]
  constructor <;> apply UScalar.eq_of_val_eq <;> simpa

private abbrev mapIterator :=
  core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator
    (core.iter.traits.iterator.IteratorSliceIter AddressRange)
    new.closure.closure.Insts.CoreOpsFunctionFnMutTupleShared1AddressRangeAddressRange

private theorem collect_intersections (ranges : Slice AddressRange) (pool : AddressRange)
    (i : Nat) (acc : List AddressRange) (hi : i ≤ ranges.val.length) :
    alloc.vec.FromIteratorVec.iterToList mapIterator ⟨⟨ranges, i⟩, pool⟩ acc
      ⦃ result => result = acc.reverse ++ (ranges.val.drop i).map (fun r => intersection r pool) ⦄ := by
  rw [alloc.vec.FromIteratorVec.iterToList.eq_def]
  simp only [mapIterator,
    _root_.core.iter.adapters.map.Map.Insts.CoreIterTraitsIteratorIterator.next,
    core.slice.iter.IteratorSliceIter.next, Slice.len_val, Slice.length]
  split
  · rename_i hnext
    simp only [bind_ok,
      new.closure.closure.Insts.CoreOpsFunctionFnMutTupleShared1AddressRangeAddressRange.call_mut]
    simp only [bind_tc_eq, Aeneas.Std.bind_assoc, bind_ok]
    step with intersect_eq_spec ranges[i] pool as ⟨r, hr⟩
    subst r
    step with collect_intersections ranges pool (i + 1) (intersection ranges.val[i] pool :: acc)
      (by omega) as ⟨result, hresult⟩
    rw [hresult, List.drop_eq_getElem_cons hnext]
    simp only [List.reverse_cons, List.map_cons, List.append_assoc, List.singleton_append]
  · rename_i hdone
    simp [List.drop_eq_nil_of_le (by omega : ranges.val.length ≤ i)]
termination_by ranges.val.length - i

@[step]
private theorem intersect_mmio_spec (ranges : Slice AddressRange) (pool : AddressRange) :
    new.closure.Insts.CoreOpsFunctionFnTupleAddressRangeResultVecAddressRangeError.call ranges pool
      ⦃ result => ∃ pools, result = .Ok pools ∧ pools.val = mmioPools ranges.val pool ⦄ := by
  unfold new.closure.Insts.CoreOpsFunctionFnTupleAddressRangeResultVecAddressRangeError.call
  simp only [core.slice.Slice.is_empty, lift, bind_ok]
  split
  · rename_i he
    simp_all [mmioPools, Array.to_slice, Array.make, alloc.slice.Slice.into_vec, alloc.vec.Vec.val]
  · rename_i hn
    have hn : ranges.val ≠ [] := by simpa [Slice.length] using hn
    simp only [core.slice.Slice.iter, _root_.core.iter.traits.iterator.Iterator.map.default,
      core.iter.traits.iterator.Iterator.collect.default, alloc.vec.FromIteratorVec.from_iter,
      core.iter.traits.collect.IntoIterator.Blanket.into_iter, bind_tc_eq, Aeneas.Std.bind_assoc, bind_ok]
    step with collect_intersections ranges pool 0 [] (by omega) as ⟨rs, hrs⟩
    simp only [List.reverse_nil, List.drop_zero, List.nil_append] at hrs
    subst rs
    have hlen : (ranges.val.map (fun r => intersection r pool)).length ≤ Usize.max := by
      simp
    simp [mmioPools, hn]

private theorem mmioPools_disjoint (ranges : List AddressRange) (pool : AddressRange)
    (hd : AddressAllocator.DisjointPools ranges) :
    AddressAllocator.DisjointPools (mmioPools ranges pool) := by
  unfold mmioPools
  split
  · simp [AddressAllocator.DisjointPools]
  · intro r hr s hs hrn hsn hne
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    have hne0 : r0 ≠ s0 := by intro h; subst s0; exact hne rfl
    have := hd r0 hr0 s0 hs0
    simp only [intersection, AddressRange.isEmptyModel, AddressAllocator.DisjointRanges, val_max, val_min] at *
    have hr0n : ¬r0.end.val < r0.start.val := by scalar_tac
    have hs0n : ¬s0.end.val < s0.start.val := by scalar_tac
    have hsep := this hr0n hs0n hne0
    scalar_tac

/-- The reservation keeps the prefix and advances the remaining high pool. -/
def Reservation (original : AddressRange) (size : Option U64)
    (remaining : AddressRange) (reserved : Option AddressRange) : Prop :=
  match size, reserved with
  | none, none => remaining = original
  | some n, some r =>
      (if n.val = original.lenModel then remaining.isEmptyModel
       else remaining.start.val = original.start.val + n.val ∧ remaining.end = original.end) ∧
      (if n.val = 0 then r.isEmptyModel
       else r.start = original.start ∧ r.end.val + 1 = original.start.val + n.val)
  | _, _ => False

/-- Optional spaces are absent exactly when their configuration is absent. -/
def OptionalInitial (pool : Option AddressRange) (alignment : U64)
    (space : Option AddressAllocator) : Prop :=
  match pool, space with
  | none, none => True
  | some r, some a => AddressAllocator.initialState r a alignment ∧ AddressAllocator.WellFormed a
  | _, _ => False

/-- Unit alignment and a bound on the recorded pools. Address-allocator
    well-formedness transfers the bound to all free and allocated addresses. -/
def UnitAllocatorInvariant (limit : Nat) (a : AddressAllocator) : Prop :=
  a.min_align = 1#u64 ∧ a.preferred_align = 1#u64 ∧
  ∀ addr, AddressAllocator.Covers a.pools.val addr → addr ≤ limit

/-- IRQ alignment and pool bounds established by the constructor. -/
abbrev IrqInvariant := UnitAllocatorInvariant 1023

/-- GPE alignment and pool bounds established by the constructor. -/
abbrev GpeInvariant := UnitAllocatorInvariant 255

theorem UnitAllocatorInvariant.free_le {limit : Nat} {a : AddressAllocator}
    (h : UnitAllocatorInvariant limit a) (hwf : AddressAllocator.WellFormed a)
    {addr : Nat} (ha : AddressAllocator.Covers a.regions addr) : addr ≤ limit :=
  h.2.2 addr (hwf.free_mem_pools ha)

theorem UnitAllocatorInvariant.allocated_le {limit : Nat} {a : AddressAllocator}
    (h : UnitAllocatorInvariant limit a) (hwf : AddressAllocator.WellFormed a)
    {addr : Nat} (ha : AddressAllocator.Allocated a addr) : addr ≤ limit :=
  h.2.2 addr (hwf.allocated_mem_pools ha)

private theorem UnitAllocatorInvariant.preserved {limit : Nat} {self a : AddressAllocator}
    (h : UnitAllocatorInvariant limit self) (hpools : a.pools = self.pools)
    (hmin : a.min_align = self.min_align) (hpref : a.preferred_align = self.preferred_align) :
    UnitAllocatorInvariant limit a := by
  simpa only [UnitAllocatorInvariant, hpools, hmin, hpref] using h

private theorem initial_unit_invariant {pool : AddressRange} {a : AddressAllocator}
    (h : AddressAllocator.initialState pool a 1#u64) :
    UnitAllocatorInvariant pool.end.val a := by
  refine ⟨h.2.2.2.1, h.2.2.2.2, ?_⟩
  intro addr ⟨r, hr, ha⟩
  rw [h.1] at hr
  simp only [AddressAllocator.initialPools] at hr
  split at hr
  · simp at hr
  · have hr := List.mem_singleton.mp hr
    subst r
    exact ha.2

/-- Bus zero reserves device zero; other buses expose all 32 devices and 8 functions. -/
def pciPool (bus : U8) : AddressRange := ⟨if bus = 0#u8 then 8#u64 else 0#u64, 255#u64⟩

/-- Each PCI bus keeps its original device/function pool and alignment policy. -/
def PciAllocatorInvariant (bus : U8) (a : AddressAllocator) : Prop :=
  a.pools.val = [pciPool bus] ∧ a.min_align = 1#u64 ∧ a.preferred_align = 8#u64

private theorem initial_pci_invariant {bus : U8} {a : AddressAllocator}
    (h : AddressAllocator.initialState (pciPool bus) a 1#u64 8#u64) :
    PciAllocatorInvariant bus a := by
  refine ⟨?_, h.2.2.2.1, h.2.2.2.2⟩
  rw [h.1]
  simp only [AddressAllocator.initialPools, AddressRange.isEmptyModel, pciPool]
  split_ifs <;> simp_all

/-- Component invariants, IRQ/GPE bounds, and PCI bus pools and alignments. -/
def WellFormed (a : SystemAllocator) : Prop :=
  (∀ io ∈ a.io_address_space, AddressAllocator.WellFormed io) ∧
  (∀ mmio ∈ a.mmio_address_spaces.val, AddressAllocator.WellFormed mmio) ∧
  (∀ platform ∈ a.mmio_platform_address_spaces, AddressAllocator.WellFormed platform) ∧
  AddressAllocator.WellFormed a.irq_allocator ∧ AddressAllocator.WellFormed a.gpe_allocator ∧
  (∀ bus space, Finmap.lookup bus a.pci_allocator = some space →
    AddressAllocator.WellFormed space ∧ PciAllocatorInvariant bus space) ∧
  IrqInvariant a.irq_allocator ∧ GpeInvariant a.gpe_allocator

/-- Exact initial pools and alignments, with no allocations or PCI buses. -/
def InitialState (config : SystemAllocatorConfig) (ranges : List AddressRange)
    (pageSize : U64) (high : AddressRange) (reserved : Option AddressRange)
    (a : SystemAllocator) : Prop :=
  OptionalInitial config.io 0x400#u64 a.io_address_space ∧
  (∃ lowSpace highSpace, a.mmio_address_spaces.val = [lowSpace, highSpace] ∧
    AddressAllocator.initialStateFromList (mmioPools ranges config.low_mmio) lowSpace pageSize ∧
    AddressAllocator.initialStateFromList (mmioPools ranges high) highSpace pageSize) ∧
  OptionalInitial config.platform_mmio pageSize a.mmio_platform_address_spaces ∧
  a.reserved_region = reserved ∧ a.pci_allocator = ∅ ∧
  AddressAllocator.initialState ⟨UScalar.cast .U64 config.first_irq, 1023#u64⟩ a.irq_allocator 1#u64 ∧
  AddressAllocator.initialState ⟨0#u64, 255#u64⟩ a.gpe_allocator 1#u64 ∧
  a.next_anon_id = 0#usize ∧ WellFormed a

/-- Constructor errors in source evaluation order. The fixed I/O, IRQ, and GPE
    alignments are valid; all MMIO constructors share the page-size alignment. -/
def newError (config : SystemAllocatorConfig) (reserve : Option U64) (pageSize : U64) : Option resources.Error := do
  if let some n := reserve then
    if U64.max < config.high_mmio.lenModel then return .OutOfBounds
    if config.high_mmio.lenModel < n.val then return .OutOfSpace
  if let some io := config.io then
    if 0xffff < io.end.val then return .IOPortOutOfRange io
  AddressAllocator.newError (some pageSize) none

/-- Success establishes the requested resource layout; errors are characterized exactly. -/
def NewOutcome (config : SystemAllocatorConfig) (reserve : Option U64)
    (ranges : List AddressRange) (pageSize : U64)
    (result : core.result.Result SystemAllocator resources.Error) : Prop :=
  match newError config reserve pageSize with
  | some error => result = .Err error
  | none => ∃ a high, result = .Ok a ∧ Reservation config.high_mmio reserve high a.reserved_region ∧
      InitialState config ranges pageSize high a.reserved_region a

/-- The translated Rust `?` continuation, factored to share constructor proofs. -/
private noncomputable def andThen {T : Type}
    (input : Result (core.result.Result T resources.Error))
    (next : T → Result (core.result.Result SystemAllocator resources.Error)) :
    Result (core.result.Result SystemAllocator resources.Error) := do
  let r ← input
  let cf ← core.result.Result.Insts.CoreOpsTry.branch r
  match cf with
  | .Continue value => next value
  | .Break residual =>
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual
      SystemAllocator (core.convert.FromSame resources.Error) residual

private noncomputable def completeAllocator (config : SystemAllocatorConfig) (io : Option AddressAllocator)
    (low high : AddressAllocator) (platform : Option AddressAllocator) (reserved : Option AddressRange)
    (pci : _root_.alloc.collections.btree.map.BTreeMap U8 AddressAllocator Global) :
    Result (core.result.Result SystemAllocator resources.Error) := do
  let irqStart ← lift (UScalar.cast .U64 config.first_irq)
  andThen (AddressAllocator.new ⟨irqStart, 1023#u64⟩ (some 1#u64) none) fun irq =>
    andThen (AddressAllocator.new ⟨0#u64, 255#u64⟩ (some 1#u64) none) fun gpe =>
      ok (.Ok ⟨io, Array.make 2#usize [low, high], platform, reserved, pci, irq, gpe, 0#usize⟩)

private noncomputable def afterIo (config : SystemAllocatorConfig) (ranges : Slice AddressRange)
    (pageSize : U64) (high : AddressRange) (reserved : Option AddressRange)
    (io : Option AddressAllocator) : Result (core.result.Result SystemAllocator resources.Error) :=
  andThen (new.closure.Insts.CoreOpsFunctionFnTupleAddressRangeResultVecAddressRangeError.call ranges config.low_mmio) fun lowPools =>
    andThen (AddressAllocator.new_from_list (core.iter.traits.collect.IntoIteratorVec AddressRange)
      lowPools (some pageSize) none) fun lowSpace =>
      andThen (new.closure.Insts.CoreOpsFunctionFnTupleAddressRangeResultVecAddressRangeError.call ranges high) fun highPools =>
        andThen (AddressAllocator.new_from_list (core.iter.traits.collect.IntoIteratorVec AddressRange)
          highPools (some pageSize) none) fun highSpace => do
          let pci ← _root_.alloc.collections.btree.map.BTreeMapKVGlobal.new U8 AddressAllocator
          match config.platform_mmio with
          | none => completeAllocator config io lowSpace highSpace none reserved pci
          | some platform => andThen (AddressAllocator.new platform (some pageSize) none) fun space =>
              completeAllocator config io lowSpace highSpace (some space) reserved pci

private theorem new_success (pool : AddressRange) (alignment : U64)
    (ha : alignment.val.isPowerOfTwo) :
    AddressAllocator.new pool (some alignment) none ⦃ result =>
      ∃ a, result = .Ok a ∧ AddressAllocator.initialState pool a alignment alignment ∧
        AddressAllocator.WellFormed a ⦄ := by
  simpa [AddressAllocator.newError, ha] using AddressAllocator.new_spec pool (some alignment) none

private theorem completeAllocator_spec (config : SystemAllocatorConfig) (ranges : List AddressRange)
    (pageSize : U64) (high : AddressRange) (reserved : Option AddressRange)
    (io platform : Option AddressAllocator) (lowSpace highSpace : AddressAllocator)
    (hio : OptionalInitial config.io 0x400#u64 io)
    (hplatform : OptionalInitial config.platform_mmio pageSize platform)
    (hlow : AddressAllocator.initialStateFromList (mmioPools ranges config.low_mmio) lowSpace pageSize pageSize)
    (hhigh : AddressAllocator.initialStateFromList (mmioPools ranges high) highSpace pageSize pageSize)
    (hwl : AddressAllocator.WellFormed lowSpace) (hwh : AddressAllocator.WellFormed highSpace) :
    completeAllocator config io lowSpace highSpace platform reserved ∅ ⦃ result =>
      ∃ a, result = .Ok a ∧ InitialState config ranges pageSize high reserved a ⦄ := by
  unfold completeAllocator andThen
  simp only [lift, bind_ok]
  step with new_success ⟨UScalar.cast .U64 config.first_irq, 1023#u64⟩ 1#u64 (by decide)
    as ⟨result, irq, he, hi, hwi⟩
  subst result
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with new_success ⟨0#u64, 255#u64⟩ 1#u64 (by decide) as ⟨result, gpe, he, hg, hwg⟩
  subst result
  simp only [bind_ok, WP.spec_ok]
  refine ⟨_, rfl, hio, ⟨lowSpace, highSpace, ?_, hlow, hhigh⟩, hplatform,
    rfl, rfl, hi, hg, rfl, ?_⟩
  · simp [Array.make]
  · refine ⟨?_, ?_, ?_, hwi, hwg, ?_, initial_unit_invariant hi, initial_unit_invariant hg⟩
    · cases h : config.io <;> cases io <;> simp_all [OptionalInitial]
    · simpa [Array.make] using And.intro hwl hwh
    · cases h : config.platform_mmio <;> cases platform <;> simp_all [OptionalInitial]
    · simp

private theorem afterIo_spec (config : SystemAllocatorConfig) (ranges : Slice AddressRange)
    (pageSize : U64) (high : AddressRange) (reserved : Option AddressRange)
    (io : Option AddressAllocator) (hio : OptionalInitial config.io 0x400#u64 io)
    (hd : AddressAllocator.DisjointPools ranges.val) :
    afterIo config ranges pageSize high reserved io ⦃ result =>
      match AddressAllocator.newError (some pageSize) none with
      | some error => result = .Err error
      | none => ∃ a, result = .Ok a ∧ InitialState config ranges.val pageSize high reserved a ⦄ := by
  unfold afterIo andThen
  step with intersect_mmio_spec ranges config.low_mmio as ⟨result, lowPools, he, hlp⟩
  subst result
  simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
  step with AddressAllocator.new_from_list_spec lowPools (some pageSize) none
    (by rw [hlp]; exact mmioPools_disjoint _ _ hd)
    as ⟨result, hl⟩
  by_cases ha : pageSize.val.isPowerOfTwo
  · simp only [AddressAllocator.newError, Option.getD_some, Option.getD_none,
      ha, le_refl, and_self, ↓reduceIte] at hl ⊢
    obtain ⟨lowSpace, rfl, hlow, hwl⟩ := hl
    simp only [bind_ok]
    step with intersect_mmio_spec ranges high as ⟨result, highPools, he, hhp⟩
    subst result
    simp only [bind_ok]
    step with AddressAllocator.new_from_list_spec highPools (some pageSize) none
      (by rw [hhp]; exact mmioPools_disjoint _ _ hd)
      as ⟨result, hh⟩
    simp only [AddressAllocator.newError, Option.getD_some, Option.getD_none,
      ha, le_refl, and_self, ↓reduceIte] at hh
    obtain ⟨highSpace, rfl, hhigh, hwh⟩ := hh
    simp only [bind_ok,
      _root_.alloc.collections.btree.map.BTreeMapKVGlobal.new]
    rw [hlp] at hlow
    rw [hhp] at hhigh
    cases hp : config.platform_mmio with
    | none =>
      exact completeAllocator_spec config ranges.val pageSize high reserved io none lowSpace highSpace
        hio (by simp [OptionalInitial, hp]) hlow hhigh hwl hwh
    | some platform =>
      step with new_success platform pageSize ha as ⟨result, space, he, hs, hws⟩
      subst result
      simp only [bind_ok]
      exact completeAllocator_spec config ranges.val pageSize high reserved io (some space) lowSpace highSpace
        hio (by simpa [OptionalInitial, hp] using And.intro hs hws) hlow hhigh hwl hwh
  · simp only [AddressAllocator.newError, Option.getD_some, Option.getD_none,
      ha, false_and, ↓reduceIte] at hl ⊢
    subst result
    simp [
      core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]


private noncomputable def afterReservation (config : SystemAllocatorConfig)
    (ranges : Slice AddressRange) (pageSize : U64) (high : AddressRange)
    (reserved : Option AddressRange) : Result (core.result.Result SystemAllocator resources.Error) :=
  match config.io with
  | none => afterIo config ranges pageSize high reserved none
  | some io =>
    if io.end > 0xffff#u64 then ok (.Err (.IOPortOutOfRange io))
    else andThen (AddressAllocator.new io (some 0x400#u64) none) fun space =>
      afterIo config ranges pageSize high reserved (some space)

private theorem afterReservation_spec (config : SystemAllocatorConfig)
    (ranges : Slice AddressRange) (pageSize : U64) (high : AddressRange)
    (reserved : Option AddressRange) (hd : AddressAllocator.DisjointPools ranges.val) :
    afterReservation config ranges pageSize high reserved ⦃ result =>
      match newError config none pageSize with
      | some error => result = .Err error
      | none => ∃ a, result = .Ok a ∧ InitialState config ranges.val pageSize high reserved a ⦄ := by
  unfold afterReservation
  cases hio : config.io with
  | none =>
    have h := afterIo_spec config ranges pageSize high reserved none (by simp [OptionalInitial, hio]) hd
    simpa [newError, hio] using h
  | some io =>
    simp only
    split
    · rename_i hbad
      have hbad' : 0xffff < io.end.val := by scalar_tac
      simp [newError, hio, hbad']
    · rename_i hgood
      have hgood' : ¬0xffff < io.end.val := by scalar_tac
      unfold andThen
      step with new_success io 0x400#u64 (by decide) as ⟨result, space, he, hs, hw⟩
      subst result
      simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      have h := afterIo_spec config ranges pageSize high reserved (some space)
        (by simpa [OptionalInitial, hio] using And.intro hs hw) hd
      simpa [newError, hio, hgood'] using h

private theorem afterReservation_outcome (config : SystemAllocatorConfig)
    (reserve : Option U64) (ranges : Slice AddressRange) (pageSize : U64)
    (high : AddressRange) (reserved : Option AddressRange)
    (hd : AddressAllocator.DisjointPools ranges.val)
    (hr : Reservation config.high_mmio reserve high reserved)
    (he : newError config reserve pageSize = newError config none pageSize) :
    afterReservation config ranges pageSize high reserved ⦃ result =>
      NewOutcome config reserve ranges.val pageSize result ⦄ := by
  apply WP.spec_mono (afterReservation_spec config ranges pageSize high reserved hd)
  intro result h
  unfold NewOutcome
  rw [he]
  cases he' : newError config none pageSize with
  | some error => simpa [he'] using h
  | none =>
    simp only [he'] at h
    obtain ⟨a, rfl, ha⟩ := h
    refine ⟨a, high, rfl, ?_, ?_⟩ <;> rw [ha.2.2.2.1]
    · exact hr
    · exact ha

private theorem reserved_from_start_and_size (pool : AddressRange) (n : U64)
    (hfits : n.val ≤ pool.lenModel) :
    AddressRange.from_start_and_size pool.start n ⦃ opt =>
      ∃ r, opt = some r ∧
        (if n.val = 0 then r.isEmptyModel
         else r.start = pool.start ∧ r.end.val + 1 = pool.start.val + n.val) ⦄ := by
  apply WP.spec_mono (AddressRange.from_start_and_size_spec pool.start n)
  intro opt h
  by_cases hn : n.val = 0
  · simpa [hn] using h
  · have hpos : 0 < pool.lenModel := by omega
    have hend_bound : pool.start.val + (n.val - 1) ≤ U64.max := by
      unfold AddressRange.lenModel AddressRange.isEmptyModel at hfits hpos
      split_ifs at hfits hpos <;> scalar_tac
    simp only [hn, hend_bound, ↓reduceIte] at h ⊢
    obtain ⟨r, rfl, hstart, hend, _⟩ := h
    exact ⟨r, rfl, hstart, by omega⟩

private theorem remaining_high_mmio (pool : AddressRange) (n len : U64)
    (hlenval : len.val = pool.lenModel) (hfits : n.val ≤ pool.lenModel) :
    (if n = len then AddressRange.empty
     else do
       let i1 ← pool.start + n
       ok { pool with start := i1 }) ⦃ remaining =>
      if n.val = pool.lenModel then remaining.isEmptyModel
      else remaining.start.val = pool.start.val + n.val ∧ remaining.end = pool.end ⦄ := by
  split
  · rename_i heq
    have hn : n.val = pool.lenModel := by rw [heq, hlenval]
    step with AddressRange.empty_spec as ⟨remaining, _, _, hrem⟩
    simpa [hn] using hrem
  · rename_i hne
    have hn : n.val ≠ pool.lenModel := by
      intro h
      apply hne
      apply UScalar.eq_of_val_eq
      omega
    have hlt : n.val < pool.lenModel := by omega
    have hbound : pool.start.val + n.val ≤ U64.max := by
      unfold AddressRange.lenModel AddressRange.isEmptyModel at hlt
      split_ifs at hlt <;> scalar_tac
    step as ⟨start, hstart⟩
    simp [hn, hstart]

/-- Total correctness of construction, assuming a successful host page-size query
    and disjoint MMIO restrictions. Invalid configurations return the specified error. -/
@[step]
theorem new_spec (config : SystemAllocatorConfig) (reserve : Option U64)
    (ranges : Slice AddressRange) (hostPageSize : Usize)
    (hpage : _root_.base.sys.unix.system_info.pagesize = ok hostPageSize)
    (hd : AddressAllocator.DisjointPools ranges.val) :
    SystemAllocator.new config reserve ranges ⦃ result =>
      NewOutcome config reserve ranges.val (UScalar.cast .U64 hostPageSize) result ⦄ := by
  unfold SystemAllocator.new
  simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch]
  rw [hpage]
  simp only [bind_ok, lift]
  cases reserve with
  | none =>
    have h := afterReservation_outcome config none ranges (UScalar.cast .U64 hostPageSize)
      config.high_mmio none hd rfl rfl
    cases hio : config.io <;> cases hp : config.platform_mmio <;>
      simp only [afterReservation, afterIo, completeAllocator, andThen, lift, bind_ok, hio, hp] at h ⊢ <;>
      (convert h using 1; clear h;
        repeat' first | rfl |
          (funext x
           try (guard_hyp x : core.result.Result _ _; cases x)
           all_goals try simp only [core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
             core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual, core.convert.FromSame.from]) |
          (congr 1))
  | some n =>
    step with AddressRange.len_spec config.high_mmio as ⟨length, hlength⟩
    by_cases hlen : config.high_mmio.lenModel ≤ U64.max
    · simp only [hlen, ↓reduceIte] at hlength
      obtain ⟨len, rfl, hlenval⟩ := hlength
      simp only [core.option.Option.ok_or_some, core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
      split
      · rename_i hout
        have hout' : config.high_mmio.lenModel < n.val := by scalar_tac
        simp [NewOutcome, newError, Nat.not_lt_of_ge hlen, hout']
      · rename_i hfits
        have hfits' : n.val ≤ config.high_mmio.lenModel := by scalar_tac
        step with reserved_from_start_and_size config.high_mmio n hfits' as ⟨opt, r, hopt, hr_reserved⟩
        subst opt
        simp only [core.option.Option.ok_or_some, bind_ok]
        step with remaining_high_mmio config.high_mmio n len hlenval hfits' as ⟨high, hr_high⟩
        have hr : Reservation config.high_mmio (some n) high (some r) := ⟨hr_high, hr_reserved⟩
        have he : newError config (some n) (UScalar.cast .U64 hostPageSize) =
            newError config none (UScalar.cast .U64 hostPageSize) := by
          simp [newError, Nat.not_lt_of_ge hlen, Nat.not_lt_of_ge hfits']
        have h := afterReservation_outcome config (some n) ranges (UScalar.cast .U64 hostPageSize)
          high (some r) hd hr he
        cases hio : config.io <;> cases hp : config.platform_mmio <;>
          simp only [afterReservation, afterIo, completeAllocator, andThen, lift, bind_ok,
            core.result.Result.Insts.CoreOpsTry.branch, hio, hp] at h ⊢ <;>
          (convert h using 1; clear h;
            repeat' first | rfl |
              (funext x
               try (guard_hyp x : core.result.Result _ _; cases x)
               all_goals try simp only [bind_ok,
                 core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                 core.convert.FromSame.from]) |
              (congr 1))
    · simp only [hlen, ↓reduceIte] at hlength
      subst length
      simp [core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, NewOutcome, newError, Nat.lt_of_not_ge hlen]

/-! ### Anonymous allocation identifiers -/

/-- Return the next anonymous ID and change only the counter, provided it has not
    reached its maximum value. -/
@[step]
theorem get_anon_alloc_spec (self : SystemAllocator)
    (hnext : self.next_anon_id.val < Usize.max) :
    get_anon_alloc self ⦃ allocation a =>
      allocation = .Anon a.next_anon_id ∧
      a = { self with next_anon_id :=
        Usize.ofNatCore (self.next_anon_id.val + 1) (by scalar_tac) } ⦄ := by
  unfold get_anon_alloc
  step as ⟨next, hid⟩
  congr 1
  apply UScalar.eq_of_val_eq
  simpa using hid

/-- An exhausted counter causes arithmetic failure in the translated function. -/
theorem get_anon_alloc_overflow (self : SystemAllocator)
    (hmax : self.next_anon_id.val = Usize.max) :
    get_anon_alloc self = fail .integerOverflow := by
  unfold get_anon_alloc
  change (do
    let next ← UScalar.tryMk .Usize (self.next_anon_id.val + 1)
    ok (resources.Alloc.Anon next, { self with next_anon_id := next })) = _
  simp [UScalar.tryMk, UScalar.tryMkOpt,
    hmax, Usize.max, Usize.numBits, Result.ofOption]

/-! ### IRQ allocation -/

/-- Allocate one IRQ under the new anonymous ID, using the address allocator's
    outcome specification. Errors become `none`.
    The counter advances in both cases, and other system components are unchanged. -/
def IrqAllocationOutcome (self : SystemAllocator) (result : Option U32)
    (a : SystemAllocator) : Prop :=
  a.next_anon_id.val = self.next_anon_id.val + 1 ∧
  a = { self with next_anon_id := a.next_anon_id, irq_allocator := a.irq_allocator } ∧
  match result with
  | none => ∃ error,
      AddressAllocator.AllocationOutcome self.irq_allocator 1#u64
        (.Anon a.next_anon_id) "irq-auto" false (.Err error) a.irq_allocator
  | some irq =>
      AddressAllocator.AllocationOutcome self.irq_allocator 1#u64
        (.Anon a.next_anon_id) "irq-auto" false (.Ok (UScalar.cast .U64 irq)) a.irq_allocator

private theorem string_tag (str : Str) (tag : String)
    (hbytes : (⟨str.val.toArray.map (fun b => UInt8.ofBitVec b.bv)⟩ : ByteArray) = tag.toByteArray) :
    _root_.alloc.string.ToString.Blanket.to_string Str.Insts.CoreFmtDisplay str = ok tag := by
  simp only [_root_.alloc.string.ToString.Blanket.to_string, ↓reduceDIte, ↓reduceIte]
  rw [hbytes]
  simp [String.fromUTF8?, tag.isValidUTF8, String.fromUTF8, Result.ofOption]

private theorem irq_tag :
    _root_.alloc.string.ToString.Blanket.to_string Str.Insts.CoreFmtDisplay (toStr "irq-auto") =
      ok "irq-auto" := by
  apply string_tag
  simp only [Aeneas.Std.toStr, Slice.from_val, List.map_toArray]
  with_unfolding_all rfl

private theorem u32_into_u64 (value : U32) :
    core.convert.num.FromU64U32.from value = UScalar.cast .U64 value := by
  apply UScalar.eq_of_val_eq
  simp

private theorem allocate_unit_spec (self : AddressAllocator) (allocation : resources.Alloc)
    (tag : String) (limit : Nat) (hwf : AddressAllocator.WellFormed self)
    (hunit : UnitAllocatorInvariant limit self) :
    AddressAllocator.allocate self 1#u64 allocation tag ⦃ result a =>
      AddressAllocator.WellFormed a ∧ UnitAllocatorInvariant limit a ∧
      AddressAllocator.AllocationOutcome self 1#u64 allocation tag false result a ⦄ := by
  apply WP.spec_mono (AddressAllocator.allocate_spec self 1#u64 allocation tag hwf)
  rintro ⟨result, a⟩ h
  have hf := h.2.pools_alignments
  exact ⟨h.1, hunit.preserved hf.1 hf.2.1 hf.2.2, h.2⟩

private theorem allocated_start_u32 {self a : AddressAllocator} {allocation : resources.Alloc}
    {tag : String} {start : U64} {limit : Nat} (hwf : AddressAllocator.WellFormed self)
    (hunit : UnitAllocatorInvariant limit self)
    (hlimit : limit ≤ U32.max)
    (hout : AddressAllocator.AllocationOutcome self 1#u64 allocation tag false (.Ok start) a) :
    UScalar.cast .U64 (UScalar.cast .U32 start) = start := by
  have hbound := hunit.free_le hwf hout.covers
  have hcast : (UScalar.cast .U32 start).val = start.val := by
    rw [UScalar.cast_val_eq]
    apply Nat.mod_eq_of_lt
    scalar_tac
  apply UScalar.eq_of_val_eq
  simpa using hcast

/-- Allocate the lowest free IRQ, preserving system invariants and advancing the
    anonymous counter even when no IRQ is returned. -/
@[step]
theorem allocate_irq_spec (self : SystemAllocator) (hwf : WellFormed self)
    (hnext : self.next_anon_id.val < Usize.max) :
    allocate_irq self ⦃ result a =>
      WellFormed a ∧ IrqAllocationOutcome self result a ⦄ := by
  unfold allocate_irq
  step with get_anon_alloc_spec self hnext as ⟨id, next, hid, hnextstate⟩
  subst next
  simp only at hid
  subst id
  rw [irq_tag]
  simp only [bind_ok]
  step with allocate_unit_spec self.irq_allocator _ "irq-auto" 1023
    hwf.2.2.2.1 hwf.2.2.2.2.2.2.1
    as ⟨result, irqSpace, hwfi, hirqi, hout⟩
  have hwfa : WellFormed { self with
      next_anon_id := Usize.ofNatCore (self.next_anon_id.val + 1) (by scalar_tac)
      irq_allocator := irqSpace } :=
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwfi, hwf.2.2.2.2.1, hwf.2.2.2.2.2.1,
      hirqi, hwf.2.2.2.2.2.2.2⟩
  cases result with
  | Err error =>
    simp only [_root_.core.result.Result.map, _root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    exact ⟨hwfa, rfl, rfl, error, hout⟩
  | Ok start =>
    have hroundtrip := allocated_start_u32 hwf.2.2.2.1 hwf.2.2.2.2.2.2.1 (by norm_num [U32.max_eq]) hout
    simp only [_root_.core.result.Result.map,
      allocate_irq.closure.Insts.CoreOpsFunctionFnOnceTupleU64U32.call_once,
      _root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    refine ⟨hwfa, rfl, rfl, ?_⟩
    simpa only [hroundtrip] using hout

/-! ### IRQ release -/

/-- Release a containing allocation and discard its result. Only the IRQ allocator
    may change; the address allocator's outcome describes coalescing and error effects. -/
def IrqReleaseOutcome (self : SystemAllocator) (irq : U32) (a : SystemAllocator) : Prop :=
  a = { self with irq_allocator := a.irq_allocator } ∧
  ∃ result, AddressAllocator.ReleaseContainingOutcome self.irq_allocator
    (UScalar.cast .U64 irq) result a.irq_allocator

/-- Release preserves system invariants and changes only the IRQ allocator.
    A missing allocation is a no-op; any release error is discarded. -/
@[step]
theorem release_irq_spec (self : SystemAllocator) (irq : U32) (hwf : WellFormed self) :
    release_irq self irq ⦃ a => WellFormed a ∧ IrqReleaseOutcome self irq a ⦄ := by
  unfold release_irq
  simp only [core.convert.IntoFrom.into, bind_ok, u32_into_u64]
  step with AddressAllocator.release_containing_spec self.irq_allocator (UScalar.cast .U64 irq)
    hwf.2.2.2.1 as ⟨result, irqSpace, hwfi, hout⟩
  have hf := hout.pools_alignments
  have hirqi : IrqInvariant irqSpace :=
    hwf.2.2.2.2.2.2.1.preserved hf.1 hf.2.1 hf.2.2
  exact ⟨⟨hwf.1, hwf.2.1, hwf.2.2.1, hwfi, hwf.2.2.2.2.1, hwf.2.2.2.2.2.1,
      hirqi, hwf.2.2.2.2.2.2.2⟩,
    rfl, result, hout⟩

/-! ### IRQ reservation -/

/-- Reserve the requested IRQ under the new anonymous ID. The counter advances
    on success and failure; other system components are unchanged. -/
def IrqReservationOutcome (self : SystemAllocator) (irq : U32) (result : Bool)
    (a : SystemAllocator) : Prop :=
  a.next_anon_id.val = self.next_anon_id.val + 1 ∧
  a = { self with next_anon_id := a.next_anon_id, irq_allocator := a.irq_allocator } ∧
  let range : AddressRange := ⟨UScalar.cast .U64 irq, UScalar.cast .U64 irq⟩
  match result with
  | true => AddressAllocator.AllocationAtOutcome self.irq_allocator range
      (.Anon a.next_anon_id) "irq-fixed" (.Ok ()) a.irq_allocator
  | false => ∃ error, AddressAllocator.AllocationAtOutcome self.irq_allocator range
      (.Anon a.next_anon_id) "irq-fixed" (.Err error) a.irq_allocator

private theorem irq_fixed_tag :
    _root_.alloc.string.ToString.Blanket.to_string Str.Insts.CoreFmtDisplay (toStr "irq-fixed") =
      ok "irq-fixed" := by
  apply string_tag
  simp only [Aeneas.Std.toStr, Slice.from_val, List.map_toArray]
  with_unfolding_all rfl

private theorem irq_allocate_at_invariant {self a : AddressAllocator} {range : AddressRange}
    {allocation : resources.Alloc} {tag : String} {result : core.result.Result Unit resources.Error}
    (hirq : IrqInvariant self)
    (hout : AddressAllocator.AllocationAtOutcome self range allocation tag result a) :
    IrqInvariant a := by
  have h := hout.pools_alignments
  exact hirq.preserved h.1 h.2.1 h.2.2

/-- Reserve exactly the requested IRQ, preserving system invariants. Rejected
    reservations return `false` and preserve the IRQ allocator, but advance the counter. -/
@[step]
theorem reserve_irq_spec (self : SystemAllocator) (irq : U32) (hwf : WellFormed self)
    (hnext : self.next_anon_id.val < Usize.max) :
    reserve_irq self irq ⦃ result a =>
      WellFormed a ∧ IrqReservationOutcome self irq result a ⦄ := by
  unfold reserve_irq
  step with get_anon_alloc_spec self hnext as ⟨id, next, hid, hnextstate⟩
  subst next
  simp only at hid
  subst id
  simp only [u32_into_u64]
  rw [irq_fixed_tag]
  simp only [bind_ok]
  step with AddressAllocator.allocate_at_spec self.irq_allocator
    ⟨UScalar.cast .U64 irq, UScalar.cast .U64 irq⟩ _ "irq-fixed" hwf.2.2.2.1
    as ⟨result, irqSpace, hwfi, hout⟩
  have hirqi := irq_allocate_at_invariant hwf.2.2.2.2.2.2.1 hout
  have hwfa : WellFormed { self with
      next_anon_id := Usize.ofNatCore (self.next_anon_id.val + 1) (by scalar_tac)
      irq_allocator := irqSpace } :=
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwfi, hwf.2.2.2.2.1, hwf.2.2.2.2.2.1,
      hirqi, hwf.2.2.2.2.2.2.2⟩
  cases result with
  | Ok u =>
    cases u
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    exact ⟨hwfa, rfl, rfl, hout⟩
  | Err error =>
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    exact ⟨hwfa, rfl, rfl, error, hout⟩

/-! ### GPE allocation -/

/-- Allocate one GPE under the new anonymous ID, using the address allocator's
    outcome specification. Errors become `none`.
    The counter advances in both cases, and other system components are unchanged. -/
def GpeAllocationOutcome (self : SystemAllocator) (result : Option U32)
    (a : SystemAllocator) : Prop :=
  a.next_anon_id.val = self.next_anon_id.val + 1 ∧
  a = { self with next_anon_id := a.next_anon_id, gpe_allocator := a.gpe_allocator } ∧
  match result with
  | none => ∃ error,
      AddressAllocator.AllocationOutcome self.gpe_allocator 1#u64
        (.Anon a.next_anon_id) "gpe-auto" false (.Err error) a.gpe_allocator
  | some gpe =>
      AddressAllocator.AllocationOutcome self.gpe_allocator 1#u64
        (.Anon a.next_anon_id) "gpe-auto" false (.Ok (UScalar.cast .U64 gpe)) a.gpe_allocator

private theorem gpe_tag :
    _root_.alloc.string.ToString.Blanket.to_string Str.Insts.CoreFmtDisplay (toStr "gpe-auto") =
      ok "gpe-auto" := by
  apply string_tag
  simp only [Aeneas.Std.toStr, Slice.from_val, List.map_toArray]
  with_unfolding_all rfl

/-- Allocate the lowest free GPE, preserving system invariants and advancing the
    anonymous counter even when no GPE is returned. -/
@[step]
theorem allocate_gpe_spec (self : SystemAllocator) (hwf : WellFormed self)
    (hnext : self.next_anon_id.val < Usize.max) :
    allocate_gpe self ⦃ result a =>
      WellFormed a ∧ GpeAllocationOutcome self result a ⦄ := by
  unfold allocate_gpe
  step with get_anon_alloc_spec self hnext as ⟨id, next, hid, hnextstate⟩
  subst next
  simp only at hid
  subst id
  rw [gpe_tag]
  simp only [bind_ok]
  step with allocate_unit_spec self.gpe_allocator _ "gpe-auto" 255
    hwf.2.2.2.2.1 hwf.2.2.2.2.2.2.2
    as ⟨result, gpeSpace, hwfg, hgpei, hout⟩
  have hwfa : WellFormed { self with
      next_anon_id := Usize.ofNatCore (self.next_anon_id.val + 1) (by scalar_tac)
      gpe_allocator := gpeSpace } :=
    ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwfg, hwf.2.2.2.2.2.1,
      hwf.2.2.2.2.2.2.1, hgpei⟩
  cases result with
  | Err error =>
    simp only [_root_.core.result.Result.map, _root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    exact ⟨hwfa, rfl, rfl, error, hout⟩
  | Ok start =>
    have hroundtrip := allocated_start_u32 hwf.2.2.2.2.1 hwf.2.2.2.2.2.2.2 (by norm_num [U32.max_eq]) hout
    simp only [_root_.core.result.Result.map,
      allocate_gpe.closure.Insts.CoreOpsFunctionFnOnceTupleU64U32.call_once,
      _root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    refine ⟨hwfa, rfl, rfl, ?_⟩
    simpa only [hroundtrip] using hout

/-! ### PCI bus allocators -/

/-- Reuse the existing bus allocator, or construct its initial state. Returning the
    mutable borrow updates only this bus; `none` retains the borrowed value. -/
def PciAllocatorBorrow (self : SystemAllocator) (bus : U8) (pci_allocator : AddressAllocator)
    (back : Option AddressAllocator → SystemAllocator) : Prop :=
  (match Finmap.lookup bus self.pci_allocator with
    | some existing => pci_allocator = existing
    | none => AddressAllocator.initialState (pciPool bus) pci_allocator 1#u64 8#u64) ∧
  ∀ updated, back updated =
    { self with pci_allocator := Finmap.insert bus (updated.getD pci_allocator) self.pci_allocator }

theorem PciAllocatorBorrow.invariant {self : SystemAllocator} {bus : U8}
    {pci_allocator : AddressAllocator} {back : Option AddressAllocator → SystemAllocator}
    (h : PciAllocatorBorrow self bus pci_allocator back)
    (hwf : WellFormed self) : PciAllocatorInvariant bus pci_allocator := by
  have h := h.1
  cases he : Finmap.lookup bus self.pci_allocator with
  | none => exact initial_pci_invariant (by simpa [he] using h)
  | some existing =>
    have h := (show pci_allocator = existing from by simpa [he] using h)
    subst pci_allocator
    exact (hwf.2.2.2.2.2.1 bus existing he).2

/-- A replacement preserving the PCI bus invariant preserves system well-formedness. -/
theorem PciAllocatorBorrow.wellFormed {self : SystemAllocator} {bus : U8}
    {pci_allocator : AddressAllocator} {back : Option AddressAllocator → SystemAllocator}
    (h : PciAllocatorBorrow self bus pci_allocator back) (hwf : WellFormed self)
    (hpci : AddressAllocator.WellFormed pci_allocator) (updated : Option AddressAllocator)
    (hupdated : ∀ a ∈ updated, AddressAllocator.WellFormed a ∧ PciAllocatorInvariant bus a) :
    WellFormed (back updated) := by
  rw [h.2]
  refine ⟨hwf.1, hwf.2.1, hwf.2.2.1, hwf.2.2.2.1, hwf.2.2.2.2.1, ?_, hwf.2.2.2.2.2.2⟩
  intro key a hlookup
  by_cases he : key = bus
  · subst key
    simp only [Finmap.lookup_insert, Option.some.injEq] at hlookup
    subst a
    cases updated with
    | none => exact ⟨hpci, h.invariant hwf⟩
    | some a => exact hupdated a (by simp)
  · rw [Finmap.lookup_insert_of_ne _ he] at hlookup
    exact hwf.2.2.2.2.2.1 key a hlookup

private theorem findEntryKey_u8 (bus : U8) (keys : List U8) :
    _root_.alloc.collections.btree.map.findEntryKey
      (resources.core.borrow.Borrow.Blanket U8) core.cmp.OrdU8 bus keys =
      ok (if bus ∈ keys then some bus else none) := by
  induction keys with
  | nil => simp [_root_.alloc.collections.btree.map.findEntryKey]
  | cons key keys ih =>
    have heq : compare bus.val key.val = .eq ↔ bus = key := by
      simp [compare, compareOfLessAndEq]
      split_ifs <;> simp_all
      scalar_tac
    simp only [_root_.alloc.collections.btree.map.findEntryKey, resources.core.borrow.Borrow.Blanket,
      _root_.core.borrow.Borrow.Blanket.borrow, core.cmp.OrdU8,
      liftFun2, core.cmp.impls.OrdU8.cmp, bind_ok]
    by_cases he : bus = key
    · subst key
      simp
    · simp [heq, he, ih]

private theorem pci_entry_spec {V : Type} (allocator : core.alloc.AllocatorClone Global)
    (m : _root_.alloc.collections.btree.map.BTreeMap U8 V Global) (bus : U8) :
    _root_.alloc.collections.btree.map.BTreeMap.entry
      allocator core.cmp.OrdU8 m bus
      ⦃ entry back =>
        entry = (match Finmap.lookup bus m with
          | none => .Vacant ⟨bus, none⟩
          | some value => .Occupied ⟨bus, value⟩) ∧
        back = _root_.alloc.collections.btree.map.entryBack m bus ⦄ := by
  unfold _root_.alloc.collections.btree.map.BTreeMap.entry
  rw [findEntryKey_u8]
  split <;> simp <;> congr 2

/-- Under the well-formedness assumption, PCI allocator lookup cannot return `none`:
    existing allocators are returned unchanged, and new buses use valid alignments
    (minimum 1, preferred 8), so construction succeeds. Callers' `None` branches
    are therefore unreachable under this assumption. -/
@[step]
theorem get_pci_allocator_mut_spec (self : SystemAllocator) (bus : U8) (hwf : WellFormed self) :
    get_pci_allocator_mut self bus ⦃ result back =>
      ∃ pci_allocator, result = some pci_allocator ∧ AddressAllocator.WellFormed pci_allocator ∧
        PciAllocatorBorrow self bus pci_allocator back ⦄ := by
  unfold get_pci_allocator_mut
  step with pci_entry_spec alloc.alloc.Global.Insts.CoreAllocAllocatorClone self.pci_allocator bus
    as ⟨entry, entryBack, he, hback⟩
  subst entry entryBack
  cases hlookup : Finmap.lookup bus self.pci_allocator with
  | some pci_allocator =>
    simp only [_root_.alloc.collections.btree.map.entry.OccupiedEntry.into_mut, bind_ok]
    apply (WP.spec_ok _).mpr
    refine ⟨pci_allocator, rfl, (hwf.2.2.2.2.2.1 bus pci_allocator hlookup).1, ?_⟩
    constructor
    · simp [hlookup]
    · intro updated
      cases updated <;> simp [_root_.alloc.collections.btree.map.entryBack] <;>
        congr 1 <;> exact Subsingleton.elim _ _
  | none =>
    have hbase : (if bus = 0#u8 then ok 8#u64 else ok 0#u64) = ok (pciPool bus).start := by
      unfold pciPool
      split <;> rfl
    rw [hbase]
    simp only [bind_ok]
    step as ⟨n, hn⟩
    step as ⟨last, hlast⟩
    have hend : last = 255#u64 := by scalar_tac
    subst last
    have hpool : ({ start := (pciPool bus).start, «end» := 255#u64 } : AddressRange) = pciPool bus := rfl
    rw [hpool]
    step with AddressAllocator.new_spec (pciPool bus) (some 1#u64) (some 8#u64)
      as ⟨result, hnew⟩
    simp [AddressAllocator.newError,
      show Nat.isPowerOfTwo 1 from by decide, show Nat.isPowerOfTwo 8 from by decide] at hnew
    obtain ⟨pci_allocator, rfl, hinitial, hpci⟩ := hnew
    simp only [_root_.core.result.Result.ok, _root_.core.option.Option.Insts.CoreOpsTry_traitTryTOptionNever.branch,
      _root_.alloc.collections.btree.map.entry.VacantEntry.insert, bind_ok]
    apply (WP.spec_ok _).mpr
    refine ⟨pci_allocator, rfl, hpci, ?_⟩
    constructor
    · simpa only [hlookup] using hinitial
    · intro updated
      cases updated <;> simp [_root_.alloc.collections.btree.map.entryBack] <;>
        congr 1 <;> exact Subsingleton.elim _ _

private theorem pci_allocate_spec (self : AddressAllocator) (bus : U8)
    (allocation : resources.Alloc) (tag : String)
    (hwf : AddressAllocator.WellFormed self) (hpci : PciAllocatorInvariant bus self) :
    AddressAllocator.allocate self 1#u64 allocation tag ⦃ result a =>
      AddressAllocator.WellFormed a ∧ PciAllocatorInvariant bus a ∧
      AddressAllocator.AllocationOutcome self 1#u64 allocation tag false result a ⦄ := by
  apply WP.spec_mono (AddressAllocator.allocate_spec self 1#u64 allocation tag hwf)
  rintro ⟨result, a⟩ h
  have hf := h.2.pools_alignments
  exact ⟨h.1, by simpa only [PciAllocatorInvariant, hf.1, hf.2.1, hf.2.2] using hpci, h.2⟩

private theorem pci_allocated_bound {self a : AddressAllocator} {bus : U8}
    {allocation : resources.Alloc} {tag : String} {start : U64}
    (hwf : AddressAllocator.WellFormed self) (hpci : PciAllocatorInvariant bus self)
    (hout : AddressAllocator.AllocationOutcome self 1#u64 allocation tag false (.Ok start) a) :
    start.val ≤ 255 := by
  obtain ⟨r, hr, ha⟩ := hwf.free_mem_pools hout.covers
  rw [hpci.1] at hr
  have hr := List.mem_singleton.mp hr
  subst r
  exact ha.2

/-- Advance the anonymous ID, borrow the bus allocator, allocate a slot, and return
    the updated borrow. Under the bus invariant, the preferred alignment selects a free
    function-zero slot when one exists, falling back to another free function.
    Errors become `none`; successful slots decode to PCI addresses. -/
def PciAllocationOutcome (self : SystemAllocator) (bus : U8) (tag : String)
    (result : Option resources.pci_address.PciAddress) (a : SystemAllocator) : Prop :=
  ∃ nextId : Usize,
    nextId.val = self.next_anon_id.val + 1 ∧
    let next := { self with next_anon_id := nextId }
    ∃ before after : AddressAllocator, ∃ back : Option AddressAllocator → SystemAllocator,
      PciAllocatorBorrow next bus before back ∧
      a = back (some after) ∧
      match result with
      | none => ∃ error, AddressAllocator.AllocationOutcome before 1#u64
          (.Anon nextId) tag false (.Err error) after
      | some pci => ∃ slot : U64, pci.bus = bus ∧
          pci.dev.val = slot.val / 8 ∧ pci.func.val = slot.val % 8 ∧
          AddressAllocator.AllocationOutcome before 1#u64
            (.Anon nextId) tag false (.Ok slot) after

private theorem pci_address_spec (bus : U8) (slot : U64) (hbound : slot.val ≤ 255) :
    allocate_pci.closure.Insts.CoreOpsFunctionFnOnceTupleU64PciAddress.call_once bus slot
      ⦃ pci => pci.bus = bus ∧ pci.dev.val = slot.val / 8 ∧ pci.func.val = slot.val % 8 ⦄ := by
  unfold allocate_pci.closure.Insts.CoreOpsFunctionFnOnceTupleU64PciAddress.call_once
  step as ⟨device, hdevice, _⟩
  have hmask : (slot &&& 7#u64).val = slot.val % 8 := by
    change slot.val &&& 7 = slot.val % 8
    exact Nat.and_two_pow_sub_one_eq_mod slot.val 3
  simp only [lift, bind_ok, WP.spec_ok]
  refine ⟨trivial, ?_, ?_⟩
  · rw [UScalar.cast_val_eq, hdevice, Nat.shiftRight_eq_div_pow]
    apply Nat.mod_eq_of_lt
    scalar_tac
  · rw [UScalar.cast_val_eq, hmask]
    apply Nat.mod_eq_of_lt
    have := Nat.mod_lt slot.val (by decide : 0 < 8)
    scalar_tac

/-- Allocate with the PCI alignment policy, decode the selected device/function,
    and preserve system invariants, provided the anonymous counter is not exhausted. -/
@[step]
theorem allocate_pci_spec (self : SystemAllocator) (bus : U8) (tag : String)
    (hwf : WellFormed self) (hnext : self.next_anon_id.val < Usize.max) :
    allocate_pci self bus tag ⦃ result a =>
      WellFormed a ∧ PciAllocationOutcome self bus tag result a ⦄ := by
  unfold allocate_pci
  step with get_anon_alloc_spec self hnext as ⟨id, next, hid, hnextstate⟩
  have hwnext : WellFormed next := by simpa only [hnextstate, WellFormed] using hwf
  step with get_pci_allocator_mut_spec next bus hwnext
    as ⟨result, back, before, hresult, hwbefore, hborrow⟩
  subst result
  simp only [_root_.core.ops.try_trait.TryOptionMut0T0Mut0T0OptionNever.Blanket.branch, bind_ok]
  have hpci := hborrow.invariant hwnext
  step with pci_allocate_spec before bus id tag hwbefore hpci
    as ⟨result, after, hwafter, hpciafter, hout⟩
  have hwback := hborrow.wellFormed hwnext hwbefore (some after) (by simpa using And.intro hwafter hpciafter)
  have hcounter : next.next_anon_id.val = self.next_anon_id.val + 1 := by
    rw [hnextstate]
    rfl
  have hborrow' : PciAllocatorBorrow { self with next_anon_id := next.next_anon_id }
      bus before back := by
    simpa only [hnextstate] using hborrow
  cases result with
  | Err error =>
    simp only [_root_.core.result.Result.map, _root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    refine ⟨hwback, next.next_anon_id, hcounter, before, after, back, hborrow', rfl, error, ?_⟩
    simpa only [hid] using hout
  | Ok slot =>
    simp only [_root_.core.result.Result.map]
    step with pci_address_spec bus slot (pci_allocated_bound hwbefore hpci hout)
      as ⟨pci, hbus, hdev, hfunc⟩
    simp only [_root_.core.result.Result.ok, bind_ok, WP.spec_ok]
    refine ⟨hwback, next.next_anon_id, hcounter, before, after, back, hborrow', rfl,
      slot, hbus, hdev, hfunc, ?_⟩
    simpa only [hid] using hout

/-- Pack the device and function fields into the bus allocator's slot number. -/
def pciSlot (pci : resources.pci_address.PciAddress) : U64 :=
  U64.ofNatCore ((pci.dev.val * 8) ||| pci.func.val)
    (Nat.or_lt_two_pow (by scalar_tac) (by scalar_tac))

@[simp]
theorem pciSlot_val (pci : resources.pci_address.PciAddress) :
    (pciSlot pci).val = (pci.dev.val * 8) ||| pci.func.val := by
  simp [pciSlot]

/-- With a three-bit function number, packing gives the usual device/function index. -/
theorem pciSlot_val_of_func_lt (pci : resources.pci_address.PciAddress) (hf : pci.func.val < 8) :
    (pciSlot pci).val = pci.dev.val * 8 + pci.func.val := by
  have h := Nat.shiftLeft_add_eq_or_of_lt (i := 3) hf pci.dev.val
  simpa [Nat.shiftLeft_eq] using h.symm

private theorem pci_slot_spec (pci : resources.pci_address.PciAddress) :
    (UScalar.cast .U64 pci.dev <<< 3#i32) ⦃ device =>
      device ||| UScalar.cast .U64 pci.func = pciSlot pci ⦄ := by
  step as ⟨device, hdevice, _⟩
  have hdev : device.val = pci.dev.val * 8 := by
    simp only [Nat.shiftLeft_eq] at hdevice
    scalar_tac
  have hfunc : (UScalar.cast .U64 pci.func).val = pci.func.val := by scalar_tac
  apply UScalar.eq_of_val_eq
  simp only [UScalar.val_or, hdev, hfunc, pciSlot_val]

/-- Advance the anonymous ID, borrow the bus allocator, and reserve the packed slot.
    Fixed-address allocation determines success; the updated borrow is returned in both cases. -/
def PciReservationOutcome (self : SystemAllocator) (pci : resources.pci_address.PciAddress)
    (tag : String) (result : Bool) (a : SystemAllocator) : Prop :=
  ∃ nextId : Usize,
    nextId.val = self.next_anon_id.val + 1 ∧
    let next := { self with next_anon_id := nextId }
    ∃ before after : AddressAllocator, ∃ back : Option AddressAllocator → SystemAllocator,
      PciAllocatorBorrow next pci.bus before back ∧
      a = back (some after) ∧
      let range : AddressRange := ⟨pciSlot pci, pciSlot pci⟩
      match result with
      | true => AddressAllocator.AllocationAtOutcome before range
          (.Anon nextId) tag (.Ok ()) after
      | false => ∃ error, AddressAllocator.AllocationAtOutcome before range
          (.Anon nextId) tag (.Err error) after

/-- Reserve the requested packed slot and preserve system invariants, provided the
    anonymous counter is not exhausted. Rejections return `false` and advance the counter. -/
@[step]
theorem reserve_pci_spec (self : SystemAllocator) (pci : resources.pci_address.PciAddress)
    (tag : String) (hwf : WellFormed self) (hnext : self.next_anon_id.val < Usize.max) :
    reserve_pci self pci tag ⦃ result a =>
      WellFormed a ∧ PciReservationOutcome self pci tag result a ⦄ := by
  unfold reserve_pci
  step with get_anon_alloc_spec self hnext as ⟨id, next, hid, hnextstate⟩
  have hwnext : WellFormed next := by simpa only [hnextstate, WellFormed] using hwf
  step with get_pci_allocator_mut_spec next pci.bus hwnext
    as ⟨result, back, before, hresult, hwbefore, hborrow⟩
  subst result
  simp only [lift, bind_ok]
  step with pci_slot_spec pci as ⟨device, hslot⟩
  simp only [hslot]
  step with AddressAllocator.allocate_at_spec before ⟨pciSlot pci, pciSlot pci⟩ id tag hwbefore
    as ⟨result, after, hwafter, hout⟩
  have hf := hout.pools_alignments
  have hpciafter : PciAllocatorInvariant pci.bus after := by
    simpa only [PciAllocatorInvariant, hf.1, hf.2.1, hf.2.2] using hborrow.invariant hwnext
  have hwback := hborrow.wellFormed hwnext hwbefore (some after)
    (by simpa using And.intro hwafter hpciafter)
  have hcounter : next.next_anon_id.val = self.next_anon_id.val + 1 := by
    rw [hnextstate]
    rfl
  have hborrow' : PciAllocatorBorrow { self with next_anon_id := next.next_anon_id }
      pci.bus before back := by
    simpa only [hnextstate] using hborrow
  cases result with
  | Ok u =>
    cases u
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    refine ⟨hwback, next.next_anon_id, hcounter, before, after, back, hborrow', rfl, ?_⟩
    simpa only [hid] using hout
  | Err error =>
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    refine ⟨hwback, next.next_anon_id, hcounter, before, after, back, hborrow', rfl, error, ?_⟩
    simpa only [hid] using hout

/-- Borrow the bus allocator and release the allocation containing the packed slot.
    The Boolean reports success, and the updated borrow is returned in both cases. -/
def PciReleaseOutcome (self : SystemAllocator) (pci : resources.pci_address.PciAddress)
    (result : Bool) (a : SystemAllocator) : Prop :=
  ∃ before after : AddressAllocator, ∃ back : Option AddressAllocator → SystemAllocator,
    PciAllocatorBorrow self pci.bus before back ∧
    a = back (some after) ∧
    match result with
    | true => ∃ released, AddressAllocator.ReleaseContainingOutcome before
        (pciSlot pci) (.Ok released) after
    | false => ∃ error, AddressAllocator.ReleaseContainingOutcome before
        (pciSlot pci) (.Err error) after

/-- Release a containing PCI allocation, preserving system invariants and the
    anonymous counter. An absent bus is initialized even when release returns `false`. -/
@[step]
theorem release_pci_spec (self : SystemAllocator) (pci : resources.pci_address.PciAddress)
    (hwf : WellFormed self) :
    release_pci self pci ⦃ result a => WellFormed a ∧ PciReleaseOutcome self pci result a ⦄ := by
  unfold release_pci
  step with get_pci_allocator_mut_spec self pci.bus hwf
    as ⟨result, back, before, hresult, hwbefore, hborrow⟩
  subst result
  simp only [lift, bind_ok]
  step with pci_slot_spec pci as ⟨device, hslot⟩
  simp only [hslot]
  step with AddressAllocator.release_containing_spec before (pciSlot pci) hwbefore
    as ⟨result, after, hwafter, hout⟩
  have hf := hout.pools_alignments
  have hpciafter : PciAllocatorInvariant pci.bus after := by
    simpa only [PciAllocatorInvariant, hf.1, hf.2.1, hf.2.2] using hborrow.invariant hwf
  have hwback := hborrow.wellFormed hwf hwbefore (some after)
    (by simpa using And.intro hwafter hpciafter)
  cases result with
  | Ok released =>
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    exact ⟨hwback, before, after, back, hborrow, rfl, released, hout⟩
  | Err error =>
    simp only [core.result.Result.is_ok, bind_ok, WP.spec_ok]
    exact ⟨hwback, before, after, back, hborrow, rfl, error, hout⟩

/-- True exactly when no allocator is recorded for the bus. -/
@[step]
theorem pci_bus_empty_spec (self : SystemAllocator) (bus : U8) :
    pci_bus_empty self bus ⦃ empty => empty = true ↔ bus ∉ self.pci_allocator ⦄ := by
  unfold pci_bus_empty _root_.alloc.collections.btree.map.BTreeMap.contains_key
  rw [findEntryKey_u8]
  by_cases h : bus ∈ self.pci_allocator <;> simp [Finmap.mem_keys, h]

/-! ### MMIO allocation -/

/-- Array position of the address space selected by the MMIO type. -/
def mmioIndex : MmioType → Usize
  | .Low => 0#usize
  | .High => 1#usize

theorem mmioIndex_lt (mmio_type : MmioType) : (mmioIndex mmio_type).val < 2 := by
  cases mmio_type <;> simp [mmioIndex]

/-- The address space selected by the MMIO type. -/
def mmioAllocator (self : SystemAllocator) (mmio_type : MmioType) : AddressAllocator :=
  self.mmio_address_spaces.val[(mmioIndex mmio_type).val]'(by simpa using mmioIndex_lt mmio_type)

private theorem mmio_address_spaces_eq (self : SystemAllocator) :
    self.mmio_address_spaces.val = [mmioAllocator self .Low, mmioAllocator self .High] := by
  obtain ⟨low, high, h⟩ := List.length_eq_two.mp self.mmio_address_spaces.property
  simp [mmioAllocator, mmioIndex, h]

/-- All configured MMIO pools, in allocator order and then in each allocator's
    pool order. Empty pool lists and repeated or empty ranges are preserved. -/
def mmioPoolList (self : SystemAllocator) : List AddressRange :=
  self.mmio_address_spaces.val.flatMap (fun allocator => allocator.pools.val)

theorem mmioPoolList_eq (self : SystemAllocator) :
    mmioPoolList self =
      (mmioAllocator self .Low).pools.val ++ (mmioAllocator self .High).pools.val := by
  simp [mmioPoolList, mmio_address_spaces_eq]

private abbrev poolIterator :=
  core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator
    (core.iter.traits.iterator.IteratorSliceIter AddressAllocator)
    (SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter AddressRange)
    mmio_pools.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressAllocatorSharedSliceAddressRange

private def remainingPools (inner : Option (core.slice.iter.Iter AddressRange)) : List AddressRange :=
  match inner with
  | none => []
  | some it => it.slice.val.drop it.i

private theorem slice_next_eq {T : Type} (it : core.slice.iter.Iter T) :
    core.slice.iter.IteratorSliceIter.next it =
      if h : it.i < it.slice.val.length then
        ok (some it.slice.val[it.i], { it with i := it.i + 1 })
      else ok (none, it) := by
  simp only [core.slice.iter.IteratorSliceIter.next, Slice.len_val, Slice.length]
  rfl

private theorem collect_mmio_pools (spaces : Slice AddressAllocator) (i : Nat)
    (inner : Option (core.slice.iter.Iter AddressRange)) (acc : List AddressRange) :
    alloc.vec.FromIteratorVec.iterToList poolIterator ⟨some ⟨spaces, i⟩, (), inner⟩ acc =
      ok (acc.reverse ++ remainingPools inner ++
        (spaces.val.drop i).flatMap (fun allocator => allocator.pools.val)) := by
  rw [alloc.vec.FromIteratorVec.iterToList.eq_def]
  simp only [poolIterator]
  rw [_root_.core.iter.adapters.flatten.FlatMap.Insts.CoreIterTraitsIteratorIterator.next.eq_def]
  cases inner with
  | some it =>
    simp only [slice_next_eq]
    split
    · rename_i hnext
      simp only [bind_tc_eq, uncurry, bind_ok]
      rw [collect_mmio_pools spaces i (some { it with i := it.i + 1 }) (it.slice.val[it.i] :: acc)]
      simp only [remainingPools, List.reverse_cons, List.append_assoc, List.singleton_append]
      rw [List.drop_eq_getElem_cons hnext]
    · rename_i hdone
      simp only [bind_tc_eq, uncurry, bind_ok]
      have ih := collect_mmio_pools spaces i none acc
      rw [alloc.vec.FromIteratorVec.iterToList.eq_def] at ih
      simpa only [poolIterator, remainingPools, uncurry, bind_tc_eq,
        List.drop_eq_nil_of_le (by omega : it.slice.val.length ≤ it.i), List.append_nil] using ih
  | none =>
    simp only [slice_next_eq]
    split
    · rename_i hnext
      simp only [bind_tc_eq, uncurry, bind_ok,
        mmio_pools.closure.Insts.CoreOpsFunctionFnMutTupleShared0AddressAllocatorSharedSliceAddressRange.call_mut,
        AddressAllocator.impl.pools, alloc.vec.Vec.deref,
        SharedSlice.Insts.CoreIterTraitsCollectIntoIteratorSharedIter.into_iter]
      have ih := collect_mmio_pools spaces (i + 1) (some ⟨alloc.vec.Vec.deref spaces.val[i].pools, 0⟩) acc
      rw [alloc.vec.FromIteratorVec.iterToList.eq_def] at ih
      rw [List.drop_eq_getElem_cons hnext]
      simpa only [poolIterator, remainingPools, uncurry, bind_tc_eq, List.drop_zero, List.flatMap_cons,
        List.append_nil, List.append_assoc, alloc.vec.Vec.deref, Slice.from_val] using ih
    · rename_i hdone
      simp [remainingPools, List.drop_eq_nil_of_le (by omega : spaces.val.length ≤ i)]
termination_by (spaces.val.length - i,
  match inner with | none => 0 | some it => it.slice.val.length - it.i + 1)
decreasing_by all_goals simp_wf <;> omega

/-- The accessor returns the configured pools in low-then-high order. The bound
    ensures that the concatenated list fits the vector model. -/
@[step]
theorem mmio_pools_spec (self : SystemAllocator) (hsize : (mmioPoolList self).length ≤ Usize.max) :
    mmio_pools self ⦃ pools => pools.val = mmioPoolList self ⦄ := by
  unfold mmio_pools
  simp only [Array.to_slice, lift, core.slice.Slice.iter,
    _root_.core.iter.traits.iterator.Iterator.flat_map.default,
    core.iter.traits.iterator.Iterator.collect.default, alloc.vec.FromIteratorVec.from_iter,
    core.iter.traits.collect.IntoIterator.Blanket.into_iter,
    bind_tc_eq, bind_ok]
  rw [collect_mmio_pools]
  simp [remainingPools, mmioPoolList] at hsize ⊢
  simp [hsize]

/-- Borrow the low and high MMIO allocators, in that order, preserving their
    complete states. Returning any two-component set writes its components back
    in the same order and preserves every other system field. The length condition
    expresses the fixed extent of the Rust slice borrowed from the MMIO array. -/
def MmioAllocatorSetBorrow (self : SystemAllocator) (allocators : AddressAllocatorSet)
    (back : AddressAllocatorSet → SystemAllocator) : Prop :=
  allocators.allocators.val = [mmioAllocator self .Low, mmioAllocator self .High] ∧
  ∀ (updated : AddressAllocatorSet) (hlen : updated.allocators.val.length = 2),
    back updated =
      { self with mmio_address_spaces := Array.from updated.allocators.val (by simpa using hlen) }

theorem MmioAllocatorSetBorrow.length {self allocators back}
    (h : MmioAllocatorSetBorrow self allocators back) : allocators.allocators.val.length = 2 := by
  simp [h.1]

/-- Borrowing and returning the original set leaves the entire system unchanged. -/
theorem MmioAllocatorSetBorrow.unchanged {self allocators back}
    (h : MmioAllocatorSetBorrow self allocators back) : back allocators = self := by
  rw [h.2 allocators h.length]
  have heq : Array.from allocators.allocators.val (by simpa using h.length) =
      self.mmio_address_spaces := by
    apply Aeneas.Std.Array.ext
    simpa only [Array.from_val, mmio_address_spaces_eq] using h.1
  simp only [heq]

/-- System well-formedness supplies exactly the component assumptions needed by
    the existing allocator-set operation specifications. -/
theorem MmioAllocatorSetBorrow.wellFormed {self allocators back}
    (h : MmioAllocatorSetBorrow self allocators back) (hwf : WellFormed self) :
    AddressAllocatorSet.WellFormed allocators := by
  have heq : allocators.allocators.val = self.mmio_address_spaces.val :=
    h.1.trans (mmio_address_spaces_eq self).symm
  intro allocator hmem
  exact hwf.2.1 allocator (heq ▸ hmem)

/-- Writing back two well-formed components preserves system well-formedness. -/
theorem MmioAllocatorSetBorrow.wellFormed_back {self allocators back}
    (h : MmioAllocatorSetBorrow self allocators back) (hwf : WellFormed self)
    (updated : AddressAllocatorSet) (hlen : updated.allocators.val.length = 2)
    (hupdated : AddressAllocatorSet.WellFormed updated) : WellFormed (back updated) := by
  rw [h.2 updated hlen]
  refine ⟨hwf.1, ?_, hwf.2.2⟩
  simpa only [AddressAllocatorSet.WellFormed, Array.from_val] using hupdated

/-- The accessor always succeeds, with the low-before-high order used by set
    operations and exact mutable write-back. No well-formedness assumption is needed. -/
@[step]
theorem mmio_allocator_any_spec (self : SystemAllocator) :
    mmio_allocator_any self ⦃ allocators back => MmioAllocatorSetBorrow self allocators back ⦄ := by
  unfold mmio_allocator_any
  step with Array.to_slice_mut_spec self.mmio_address_spaces
    as ⟨slice, arrayBack, hslice, harrayBack⟩
  step with AddressAllocatorSet.new_spec slice as ⟨allocators, setBack, hset, hsetBack⟩
  refine ⟨?_, ?_⟩
  · rw [hset, hslice, mmio_address_spaces_eq]
  · intro updated hlen
    simp only [hsetBack, harrayBack]
    simp [Array.from_slice, hlen]

/-- Replace the address space selected by the MMIO type. -/
def setMmioAllocator (self : SystemAllocator) (mmio_type : MmioType)
    (space : AddressAllocator) : SystemAllocator :=
  { self with mmio_address_spaces := self.mmio_address_spaces.set (mmioIndex mmio_type) space }

theorem mmioAllocator_wellFormed {self : SystemAllocator} (hwf : WellFormed self)
    (mmio_type : MmioType) : AddressAllocator.WellFormed (mmioAllocator self mmio_type) :=
  hwf.2.1 _ (List.getElem_mem _)

/-- Replacing an MMIO space by a well-formed one preserves system well-formedness. -/
theorem setMmioAllocator_wellFormed {self : SystemAllocator} {space : AddressAllocator}
    (hwf : WellFormed self) (mmio_type : MmioType) (hspace : AddressAllocator.WellFormed space) :
    WellFormed (setMmioAllocator self mmio_type space) := by
  obtain ⟨hio, hmmio, hrest⟩ := hwf
  refine ⟨hio, ?_, hrest⟩
  intro mmio hmem
  simp only [setMmioAllocator, Array.set_val_eq] at hmem
  rcases List.mem_or_eq_of_mem_set hmem with h | h
  · exact hmmio mmio h
  · exact h ▸ hspace

/-- Allocate from the selected MMIO space in the requested search direction, with the
    explicit alignment or the preferred-alignment fallback, and write the updated space back. -/
def MmioAllocationOutcome (self : SystemAllocator) (size : U64) (allocation : resources.Alloc)
    (tag : String) (opts : AllocOptions) (mmio_type : MmioType)
    (result : core.result.Result U64 resources.Error) (a : SystemAllocator) : Prop :=
  let space := mmioAllocator self mmio_type
  ∃ after : AddressAllocator,
    a = setMmioAllocator self mmio_type after ∧
    match opts.alignment with
    | some align => AddressAllocator.AlignedAllocationOutcome space size allocation tag
        align.val opts.top_down result after
    | none => AddressAllocator.AllocationOutcome space size allocation tag opts.top_down result after

/-- Every expected MMIO allocation error leaves the entire system unchanged. -/
theorem MmioAllocationOutcome.eq_of_err {self a : SystemAllocator} {size : U64}
    {allocation : resources.Alloc} {tag : String} {opts : AllocOptions} {mmio_type : MmioType}
    {error : resources.Error}
    (h : MmioAllocationOutcome self size allocation tag opts mmio_type (.Err error) a) :
    a = self := by
  obtain ⟨after, rfl, h⟩ := h
  have heq : after = mmioAllocator self mmio_type := by
    cases ha : opts.alignment <;> simp only [ha] at h <;> exact h.eq_of_err
  rw [heq]
  have hset : self.mmio_address_spaces.set (mmioIndex mmio_type)
      (mmioAllocator self mmio_type) = self.mmio_address_spaces :=
    Array.set_getElem_eq _ _ (by simpa using mmioIndex_lt mmio_type)
  simp only [setMmioAllocator, hset]

/-- A successful allocation's inclusive endpoint lies in the selected original pool. -/
theorem MmioAllocationOutcome.end_mem_pools {self a : SystemAllocator} {size start : U64}
    {allocation : resources.Alloc} {tag : String} {opts : AllocOptions} {mmio_type : MmioType}
    (h : MmioAllocationOutcome self size allocation tag opts mmio_type (.Ok start) a)
    (hwf : WellFormed self) :
    AddressAllocator.Covers (mmioAllocator self mmio_type).pools.val
      (start.val + (size.val - 1)) := by
  obtain ⟨after, _, h⟩ := h
  apply (mmioAllocator_wellFormed hwf mmio_type).free_mem_pools
  cases ha : opts.alignment <;> simp only [ha] at h
  case none => exact h.end_covers
  case some align => exact h.placement.end_covers

private theorem mmio_index_spec (mmio_type : MmioType) :
    lift (IScalar.hcast .Usize (read_discriminant mmio_type)) ⦃ i => i = mmioIndex mmio_type ⦄ := by
  apply WP.spec_mono (IScalar.hcast_inBounds_spec .Usize _ ?_)
  · intro i hi
    apply UScalar.eq_of_val_eq
    cases mmio_type <;> simp [mmioIndex, read_discriminant, MmioType.read_discriminant] at hi ⊢ <;>
      omega
  · cases mmio_type <;> simp [read_discriminant, MmioType.read_discriminant]; scalar_tac

/-- Allocate with the requested options from the selected MMIO space, preserving
    system invariants. The address-allocator contract determines success and errors. -/
@[step]
theorem allocate_mmio_internal_spec (self : SystemAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (opts : AllocOptions) (mmio_type : MmioType)
    (hwf : WellFormed self) :
    allocate_mmio_internal self size allocation tag opts mmio_type ⦃ result a =>
      WellFormed a ∧ MmioAllocationOutcome self size allocation tag opts mmio_type result a ⦄ := by
  unfold allocate_mmio_internal
  step with mmio_index_spec mmio_type as ⟨i, hi⟩
  subst i
  step with Array.index_mut_usize_spec self.mmio_address_spaces (mmioIndex mmio_type)
    (by simpa using mmioIndex_lt mmio_type) as ⟨space, back, hspace, hback⟩
  subst space back
  rw [← mmioAllocator]
  have hwspace := mmioAllocator_wellFormed hwf mmio_type
  obtain ⟨_, _, alignment, top_down⟩ := opts
  cases alignment with
  | none =>
    cases top_down <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · step with AddressAllocator.allocate_spec (mmioAllocator self mmio_type) size allocation tag hwspace
        as ⟨result, after, hwafter, hout⟩
      exact ⟨setMmioAllocator_wellFormed hwf mmio_type hwafter, after, rfl, hout⟩
    · step with AddressAllocator.reverse_allocate_spec (mmioAllocator self mmio_type) size allocation tag
        hwspace as ⟨result, after, hwafter, hout⟩
      exact ⟨setMmioAllocator_wellFormed hwf mmio_type hwafter, after, rfl, hout⟩
  | some align =>
    cases top_down <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · step with AddressAllocator.allocate_with_align_spec (mmioAllocator self mmio_type) size allocation
        tag align hwspace as ⟨result, after, hwafter, hout⟩
      exact ⟨setMmioAllocator_wellFormed hwf mmio_type hwafter, after, rfl, hout⟩
    · step with AddressAllocator.reverse_allocate_with_align_spec (mmioAllocator self mmio_type) size
        allocation tag align hwspace as ⟨result, after, hwafter, hout⟩
      exact ⟨setMmioAllocator_wellFormed hwf mmio_type hwafter, after, rfl, hout⟩

/-- Only unrestricted, prefetchable requests prefer the high address space. -/
def preferredMmioType (opts : AllocOptions) : MmioType :=
  if opts.max_address.val < U64.max ∨ opts.prefetchable = false then .Low else .High

open scoped Classical in
/-- Public MMIO policy: reject sub-32-bit limits, then allocate in the preferred
    space. Only high-space exhaustion retries in low space. Each attempt reuses
    the internal allocation contract, including alignment, ordering, and state updates. -/
def MmioRequestOutcome (self : SystemAllocator) (size : U64) (allocation : resources.Alloc)
    (tag : String) (opts : AllocOptions) (result : core.result.Result U64 resources.Error)
    (a : SystemAllocator) : Prop :=
  if opts.max_address.val < U32.max then result = .Err .OutOfSpace ∧ a = self
  else ∃ (first : core.result.Result U64 resources.Error) (tried : SystemAllocator),
    MmioAllocationOutcome self size allocation tag opts (preferredMmioType opts) first tried ∧
    if preferredMmioType opts = .High ∧ first = .Err .OutOfSpace then
      MmioAllocationOutcome tried size allocation tag opts .Low result a
    else result = first ∧ a = tried

/-- Public MMIO allocation preserves the entire system on every expected error. -/
theorem MmioRequestOutcome.eq_of_err {self a : SystemAllocator} {size : U64}
    {allocation : resources.Alloc} {tag : String} {opts : AllocOptions} {error : resources.Error}
    (h : MmioRequestOutcome self size allocation tag opts (.Err error) a) : a = self := by
  unfold MmioRequestOutcome at h
  split at h
  · exact h.2
  · obtain ⟨first, tried, hfirst, h⟩ := h
    split at h
    · rename_i hfallback
      rw [hfallback.2] at hfirst
      exact h.eq_of_err.trans hfirst.eq_of_err
    · obtain ⟨rfl, rfl⟩ := h
      exact hfirst.eq_of_err

/-- The requested inclusive address limit is respected when the low pool has its
    documented 32-bit bound. System well-formedness alone does not impose that bound. -/
theorem MmioRequestOutcome.end_le_max_address {self a : SystemAllocator} {size start : U64}
    {allocation : resources.Alloc} {tag : String} {opts : AllocOptions}
    (h : MmioRequestOutcome self size allocation tag opts (.Ok start) a)
    (hwf : WellFormed self)
    (hlow : ∀ addr, AddressAllocator.Covers (mmioAllocator self .Low).pools.val addr →
      addr ≤ U32.max) :
    start.val + size.val ≤ opts.max_address.val + 1 := by
  unfold MmioRequestOutcome at h
  split at h
  · simp at h
  · rename_i hlimit
    obtain ⟨first, tried, hfirst, h⟩ := h
    split at h
    · rename_i hfallback
      rw [hfallback.2] at hfirst
      have htried := hfirst.eq_of_err
      subst tried
      have := hlow _ (h.end_mem_pools hwf)
      omega
    · obtain ⟨rfl, rfl⟩ := h
      have hend := hfirst.end_mem_pools hwf
      unfold preferredMmioType at hend
      split at hend
      · have := hlow _ hend
        omega
      · rename_i hhigh
        obtain ⟨slot, _, hslot⟩ := hend
        have hbound : slot.end.val ≤ U64.max := by scalar_tac
        simp only [AddressRange.containsModel] at hslot
        omega

private theorem mmio_type_eq_spec (left right : MmioType) :
    MmioType.Insts.CoreCmpPartialEqMmioType.eq left right
      ⦃ equal => equal = true ↔ left = right ⦄ := by
  cases left <;> cases right <;>
    simp [MmioType.Insts.CoreCmpPartialEqMmioType.eq, MmioType.read_discriminant]

/-- Total correctness of public MMIO allocation, including space selection,
    high-to-low fallback, alignment, search direction, and invariant preservation. -/
@[step]
theorem allocate_mmio_spec (self : SystemAllocator) (size : U64)
    (allocation : resources.Alloc) (tag : String) (opts : AllocOptions)
    (hwf : WellFormed self) :
    allocate_mmio self size allocation tag opts ⦃ result a =>
      WellFormed a ∧ MmioRequestOutcome self size allocation tag opts result a ⦄ := by
  unfold allocate_mmio
  step with UScalar.cast_inBounds_spec .U64 core.num.U32.MAX
    (by simp [core.num.U32.MAX, U32.rMax, U64.max_eq])
    as ⟨limit, hlimit⟩
  have hlimit : limit.val = U32.max := by
    simpa [core.num.U32.MAX, U32.max_eq, U32.rMax] using hlimit
  split
  · rename_i hsmall
    have hsmall : opts.max_address.val < U32.max := by scalar_tac
    simp only [WP.spec_ok]
    exact ⟨hwf, by simp [MmioRequestOutcome, hsmall]⟩
  · rename_i hlarge
    have hlarge : ¬opts.max_address.val < U32.max := by scalar_tac
    have hselect :
        (if opts.max_address < core.num.U64.MAX then ok MmioType.Low
         else if opts.prefetchable then ok MmioType.High else ok MmioType.Low) =
        ok (preferredMmioType opts) := by
      simp only [preferredMmioType, core.num.U64.MAX, UScalar.lt_equiv]
      cases opts.prefetchable <;> simp [U64.max_eq, U64.rMax]
      split <;> simp_all
    rw [hselect]
    simp only [bind_ok, alloc.string.String.Insts.CoreCloneClone.clone]
    step with allocate_mmio_internal_spec self size allocation tag opts (preferredMmioType opts) hwf
      as ⟨first, tried, hwtried, hfirst⟩
    step with mmio_type_eq_spec (preferredMmioType opts) .High as ⟨high, hhigh⟩
    split
    · rename_i hhigh'
      have hhigh' := hhigh.mp hhigh'
      cases first with
      | Ok start =>
        simp only [bind_ok]
        change (ok (.Ok start, tried)) ⦃ result a =>
          WellFormed a ∧ MmioRequestOutcome self size allocation tag opts result a ⦄
        simp only [WP.spec_ok]
        exact ⟨hwtried, by
          simp only [MmioRequestOutcome, hlarge, ↓reduceIte]
          exact ⟨.Ok start, tried, hfirst, by simp⟩⟩
      | Err error =>
        cases error <;> simp only [bind_ok]
        all_goals first
          | (change allocate_mmio_internal tried size allocation tag opts .Low ⦃ result a =>
               WellFormed a ∧ MmioRequestOutcome self size allocation tag opts result a ⦄
             step with allocate_mmio_internal_spec tried size allocation tag opts .Low hwtried
              as ⟨result, a, hwa, hout⟩
             exact ⟨hwa, by
               simp only [MmioRequestOutcome, hlarge, ↓reduceIte]
               exact ⟨.Err .OutOfSpace, tried, hfirst, by simpa [hhigh'] using hout⟩⟩)
          | (change (ok (_, tried)) ⦃ result a =>
               WellFormed a ∧ MmioRequestOutcome self size allocation tag opts result a ⦄
             simp only [WP.spec_ok]
             exact ⟨hwtried, by
               simp only [MmioRequestOutcome, hlarge, ↓reduceIte]
               exact ⟨_, tried, hfirst, by simp⟩⟩)
    · rename_i hlow
      have hlow : preferredMmioType opts ≠ .High := by simp_all
      simp only [WP.spec_ok]
      exact ⟨hwtried, by
        simp only [MmioRequestOutcome, hlarge, ↓reduceIte]
        exact ⟨first, tried, hfirst, by simp [hlow]⟩⟩


/-! ### MMIO reservation -/

set_option maxRecDepth 2048

/-- Stable pool order used for reservation, including duplicate pools. -/
def sortedMmioPools (self : SystemAllocator) : List AddressRange :=
  (mmioPoolList self).mergeSort (fun a b => a.start.val ≤ b.start.val)

/-- Exactly the nonempty intersections, in the supplied pool order. -/
def reservationOverlaps (pools : List AddressRange) (range : AddressRange) : List AddressRange :=
  pools.filterMap fun pool =>
    let overlap := intersection pool range
    if overlap.isEmptyModel then none else some overlap

/-- One reservation consumes an anonymous ID, borrows both MMIO allocators,
    and applies their fixed-address allocation contract. The borrow writes back
    the final component states, including on an expected allocation error. -/
def MmioReservationAttempt (self : SystemAllocator) (overlap : AddressRange)
    (result : core.result.Result Unit resources.Error) (a : SystemAllocator) : Prop :=
  ∃ next allocators back updated,
    next.next_anon_id.val = self.next_anon_id.val + 1 ∧
    next = { self with next_anon_id := next.next_anon_id } ∧
    MmioAllocatorSetBorrow next allocators back ∧
    AddressAllocatorSet.AllocationAtOutcome allocators overlap
      (.Anon next.next_anon_id) "pci mmio reserve" result updated ∧
    a = back updated

/-- Reserve the intersections in order, stopping at the first failed attempt.
    Successful earlier reservations remain in place; the failing attempt also
    consumes its ID. The component contract determines the returned error. -/
def MmioReservationSequence (self : SystemAllocator) : List AddressRange →
    core.result.Result Unit resources.Error → SystemAllocator → Prop
  | [], result, a => result = .Ok () ∧ a = self
  | overlap :: rest, result, a => ∃ first next,
      MmioReservationAttempt self overlap first next ∧
      match first with
      | .Ok () => MmioReservationSequence next rest result a
      | .Err error => result = .Err error ∧ a = next

/-- Reserve every nonempty pool intersection in stable ascending start order.
    Empty requests and requests outside the pools leave the entire system unchanged.
    Pools may overlap across components; errors and key collisions are described
    by the existing allocator-set contract, without assuming IDs are fresh. -/
def MmioReservationOutcome (self : SystemAllocator) (range : AddressRange)
    (result : core.result.Result Unit resources.Error) (a : SystemAllocator) : Prop :=
  MmioReservationSequence self (reservationOverlaps (sortedMmioPools self) range) result a

private abbrev reservationComparator :=
  reserve_mmio.closure.Insts.CoreOpsFunctionFnMutPairShared0AddressRangeShared1AddressRangeOrdering

private theorem reservation_compare (x y : AddressRange) :
    reservationComparator.call_mut () (x, y) = ok (compare x.start.val y.start.val, ()) := by
  simp only [reserve_mmio.closure.Insts.CoreOpsFunctionFnMutPairShared0AddressRangeShared1AddressRangeOrdering.call_mut,
    core.cmp.impls.OrdU64.cmp, lift, bind_ok, uncurry]

private theorem reservation_sort_le (x y : AddressRange) :
    alloc.slice.sortLe reservationComparator () x y = decide (x.start.val ≤ y.start.val) := by
  unfold alloc.slice.sortLe
  rw [reservation_compare]
  simp [Nat.compare_ne_gt]

private theorem reservation_sort_spec (pools : Slice AddressRange) :
    alloc.slice.Slice.sort_by reservationComparator pools () ⦃ sorted =>
      sorted.val = pools.val.mergeSort (fun a b => a.start.val ≤ b.start.val) ⦄ := by
  have hpure : ∀ x y : AddressRange, ∃ order,
      reservationComparator.call_mut () (x, y) = ok (order, ()) ∧
      reservationComparator.call_mut () (y, x) = ok (order.swap, ()) := by
    intro x y
    exact ⟨compare x.start.val y.start.val, reservation_compare x y,
      by rw [reservation_compare, Nat.compare_swap]⟩
  have hle : alloc.slice.sortLe reservationComparator () =
      (fun a b : AddressRange => decide (a.start.val ≤ b.start.val)) :=
    funext fun x => funext fun y => reservation_sort_le x y
  have htrans : ∀ x y z, alloc.slice.sortLe reservationComparator () x y →
      alloc.slice.sortLe reservationComparator () y z →
      alloc.slice.sortLe reservationComparator () x z := by
    simp only [hle, decide_eq_true_eq]
    exact fun _ _ _ => Nat.le_trans
  unfold alloc.slice.Slice.sort_by
  rw [if_pos ⟨hpure, htrans⟩]
  simp only [WP.spec_ok, Slice.from_val, hle]

private theorem copy_reservation_pools_spec (iter : alloc.vec.Vec AddressRange)
    (pools : alloc.vec.Vec AddressRange)
    (hsize : pools.val.length + iter.val.length ≤ Usize.max) :
    reserve_mmio_loop0 iter pools ⦃ copied => copied.val = pools.val ++ iter.val ⦄ := by
  unfold reserve_mmio_loop0
  rw [loop.eq_def]
  dsimp only
  rw [reserve_mmio_loop0.body, alloc.vec.into_iter.IteratorIntoIter.next]
  split
  · rename_i hi
    change iter.val = [] at hi
    simp [bind_ok, uncurry, hi]
  · rename_i pool rest hi
    change iter.val = pool :: rest at hi
    simp only [bind_ok, uncurry]
    step with alloc.vec.Vec.push_spec pools pool (by simp only [hi, List.length_cons] at hsize; omega)
      as ⟨pushed, hpushed⟩
    have hrest : rest.length ≤ Usize.max := by
      simp only [hi, List.length_cons] at hsize
      omega
    change reserve_mmio_loop0 (alloc.vec.Vec.from rest hrest) pushed
      ⦃ copied => copied.val = pools.val ++ iter.val ⦄
    apply WP.spec_mono (copy_reservation_pools_spec (alloc.vec.Vec.from rest hrest) pushed
      (by
        simp only [alloc.vec.Vec.from_val, hpushed, List.length_append,
          hi, List.length_cons, List.length_nil] at hsize ⊢
        omega))
    intro copied hcopied
    simpa [hpushed, hi, List.append_assoc] using hcopied

termination_by iter.val.length
decreasing_by
  simp_wf
  simp_all only [List.length_cons]
  omega

private theorem reservation_tag :
    _root_.alloc.string.ToString.Blanket.to_string Str.Insts.CoreFmtDisplay
      (toStr "pci mmio reserve") = ok "pci mmio reserve" := by
  apply string_tag
  simp only [Aeneas.Std.toStr, Slice.from_val, List.map_toArray]
  with_unfolding_all rfl

/-- Each attempt advances only the counter and the MMIO components. -/
theorem MmioReservationAttempt.frame {self a : SystemAllocator} {overlap result}
    (h : MmioReservationAttempt self overlap result a) :
    a.next_anon_id.val = self.next_anon_id.val + 1 ∧
    a = { self with next_anon_id := a.next_anon_id, mmio_address_spaces := a.mmio_address_spaces } := by
  obtain ⟨next, allocators, back, updated, hcounter, hnext, hborrow, hout, rfl⟩ := h
  rw [hborrow.2 updated (hout.length.trans hborrow.length)]
  constructor
  · exact hcounter
  · exact congrArg (fun s : SystemAllocator => { s with
      next_anon_id := next.next_anon_id
      mmio_address_spaces := Array.from updated.allocators.val
        (by simpa using hout.length.trans hborrow.length) }) hnext

/-- A rejected attempt changes only the anonymous counter. Earlier successful
    attempts in a sequence are not rolled back. -/
theorem MmioReservationAttempt.error_state {self a : SystemAllocator} {overlap error}
    (h : MmioReservationAttempt self overlap (.Err error) a) :
    a = { self with next_anon_id := a.next_anon_id } := by
  obtain ⟨next, allocators, back, updated, _, hnext, hborrow, hout, rfl⟩ := h
  rw [hout.error_unchanged, hborrow.unchanged]
  exact hnext


@[simp] private theorem reservationOverlaps_cons (pool : AddressRange) (rest : List AddressRange)
    (range : AddressRange) :
    reservationOverlaps (pool :: rest) range =
      if (intersection pool range).isEmptyModel then reservationOverlaps rest range
      else intersection pool range :: reservationOverlaps rest range := by
  by_cases h : (intersection pool range).isEmptyModel <;> simp [reservationOverlaps, h]

private theorem reservationOverlaps_after (pools : List AddressRange) (range : AddressRange)
    (hafter : ∀ pool ∈ pools, range.end.val < pool.start.val) :
    reservationOverlaps pools range = [] := by
  simp only [reservationOverlaps, List.filterMap_eq_nil_iff]
  intro pool hp
  have := hafter pool hp
  simp only [intersection, AddressRange.isEmptyModel, val_min, val_max]
  simp [show min pool.end.val range.end.val < max pool.start.val range.start.val by omega]

private theorem reserve_mmio_loop_spec (pools : Slice AddressRange) (i : Nat)
    (self : SystemAllocator) (range : AddressRange) (hwf : WellFormed self)
    (hsorted : (pools.val.drop i).Pairwise (fun a b => a.start.val ≤ b.start.val))
    (hnext : self.next_anon_id.val + (reservationOverlaps (pools.val.drop i) range).length ≤ Usize.max) :
    reserve_mmio_loop1 ⟨pools, i⟩ self range ⦃ result a =>
      WellFormed a ∧ MmioReservationSequence self (reservationOverlaps (pools.val.drop i) range) result a ⦄ := by
  unfold reserve_mmio_loop1
  rw [loop.eq_def]
  dsimp only
  rw [reserve_mmio_loop1.body, slice_next_eq]
  dsimp only
  split
  · rename_i hi
    change i < pools.val.length at hi
    have hdrop := List.drop_eq_getElem_cons hi
    rw [hdrop, List.pairwise_cons] at hsorted
    simp only [bind_ok, uncurry]
    split
    · rename_i hafter
      have hafter : range.end.val < pools.val[i].start.val := by scalar_tac
      have hnone : reservationOverlaps (pools.val.drop i) range = [] :=
        reservationOverlaps_after _ _ (by
          rw [hdrop]
          intro pool hp
          rcases List.mem_cons.mp hp with rfl | hp
          · exact hafter
          · exact Nat.lt_of_lt_of_le hafter (hsorted.1 pool hp))
      simp [hnone, MmioReservationSequence, hwf]
    · step with intersect_eq_spec pools.val[i] range as ⟨overlap, hoverlap⟩
      subst overlap
      step with AddressRange.is_empty_spec (intersection pools.val[i] range) as ⟨empty, hempty⟩
      split
      · rename_i he
        have he := hempty.mp he
        have hoverlaps : reservationOverlaps (pools.val.drop i) range =
            reservationOverlaps (pools.val.drop (i + 1)) range := by simp only [hdrop, reservationOverlaps_cons, if_pos he]
        simp only [bind_ok]
        rw [hoverlaps] at hnext ⊢
        exact reserve_mmio_loop_spec pools (i + 1) self range hwf hsorted.2 hnext
      · rename_i hn
        have hn : ¬(intersection pools.val[i] range).isEmptyModel := fun he => hn (hempty.mpr he)
        have hoverlaps : reservationOverlaps (pools.val.drop i) range =
            intersection pools.val[i] range :: reservationOverlaps (pools.val.drop (i + 1)) range := by
          simp only [hdrop, reservationOverlaps_cons, if_neg hn]
        rw [hoverlaps] at hnext ⊢
        step with get_anon_alloc_spec self (by simp only [List.length_cons] at hnext; omega)
          as ⟨pair, hid, hnextstate⟩
        rcases pair with ⟨id, next⟩
        dsimp only at hid hnextstate
        simp only [uncurry]
        have hcounter : next.next_anon_id.val = self.next_anon_id.val + 1 := by simp [hnextstate]
        have hnextframe : next = { self with next_anon_id := next.next_anon_id } := by simp [hnextstate]
        have hwnext : WellFormed next := by simpa only [hnextstate, WellFormed] using hwf
        subst id
        step with mmio_allocator_any_spec next as ⟨pair, hborrow⟩
        rcases pair with ⟨allocators, back⟩
        dsimp only at hborrow
        simp only [uncurry]
        rw [reservation_tag]
        simp only [bind_ok]
        step with AddressAllocatorSet.allocate_at_spec allocators (intersection pools.val[i] range)
          (.Anon next.next_anon_id) "pci mmio reserve" (hborrow.wellFormed hwnext)
          as ⟨triple, hwupdated, hout, hback⟩
        rcases triple with ⟨first, updated, allocationBack⟩
        dsimp only at hwupdated hout hback
        simp only [uncurry]
        have hwfinal := hborrow.wellFormed_back hwnext updated
          (hout.length.trans hborrow.length) hwupdated
        have hattempt : MmioReservationAttempt self (intersection pools.val[i] range) first (back updated) :=
          ⟨next, allocators, back, updated, hcounter, hnextframe, hborrow, hout, rfl⟩
        simp only [hback]
        cases first with
        | Err error =>
          simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
            core.result.Result.Insts.CoreOpsTry.branch, bind_ok,
            core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            core.convert.FromSame.from, bind_tc_eq, WP.spec_ok]
          exact ⟨hwfinal, .Err error, back updated, hattempt, rfl, rfl⟩
        | Ok u =>
          cases u
          simp only [core.result.Result.Insts.CoreOpsTry_traitTryTResultNeverE.branch,
            core.result.Result.Insts.CoreOpsTry.branch, bind_ok]
          change reserve_mmio_loop1 ⟨pools, i + 1⟩ (back updated) range ⦃ result a =>
            WellFormed a ∧ MmioReservationSequence self
              (intersection pools.val[i] range :: reservationOverlaps (pools.val.drop (i + 1)) range) result a ⦄
          apply WP.spec_mono (reserve_mmio_loop_spec pools (i + 1) (back updated) range hwfinal hsorted.2
            (by have hc := hattempt.frame.1; simp only [List.length_cons] at hnext; omega))
          rintro ⟨result, a⟩ ⟨hwa, hrest⟩
          exact ⟨hwa, .Ok (), back updated, hattempt, hrest⟩
  · rename_i hi
    change ¬i < pools.val.length at hi
    simp [List.drop_eq_nil_of_le (by omega : pools.val.length ≤ i),
      reservationOverlaps, MmioReservationSequence, hwf]
termination_by pools.val.length - i

/-- Total correctness of reservation, including partial updates on errors. The
    pool-count bound permits vector collection; the anonymous-ID budget is one
    per nonempty intersection (including a possible failing final attempt).
    No freshness, cross-component pool disjointness, or endpoint arithmetic
    assumptions are required. Empty ranges and `u64::MAX` endpoints are covered. -/
@[step]
theorem reserve_mmio_spec (self : SystemAllocator) (range : AddressRange)
    (hwf : WellFormed self) (hsize : (mmioPoolList self).length ≤ Usize.max)
    (hnext : self.next_anon_id.val +
      (reservationOverlaps (sortedMmioPools self) range).length ≤ Usize.max) :
    reserve_mmio self range ⦃ result a =>
      WellFormed a ∧ MmioReservationOutcome self range result a ⦄ := by
  unfold reserve_mmio
  step with mmio_pools_spec self hsize as ⟨original, horiginal⟩
  simp only [alloc.vec.IntoIteratorVec.into_iter, bind_ok]
  step with copy_reservation_pools_spec original (alloc.vec.Vec.new AddressRange)
    (by simpa [horiginal] using hsize) as ⟨copied, hcopied⟩
  have hcopied : copied.val = mmioPoolList self := by simpa [horiginal] using hcopied
  simp only [alloc.vec.Vec.deref_mut, lift, bind_ok]
  step with reservation_sort_spec copied.slice as ⟨sorted, hsorted⟩
  have hsorted : sorted.val = sortedMmioPools self := by
    simpa [sortedMmioPools, ← hcopied, alloc.vec.Vec.val] using hsorted
  simp only [SharedAVec.Insts.CoreIterTraitsCollectIntoIteratorSharedATIter.into_iter, bind_ok]
  apply WP.spec_mono (reserve_mmio_loop_spec _ 0 self range hwf ?_ ?_)
  · rintro ⟨result, a⟩ h
    simpa [MmioReservationOutcome, alloc.vec.Vec.deref, alloc.vec.Vec.val, hsorted] using h
  · simp only [alloc.vec.Vec.deref, alloc.vec.Vec.val, Slice.from_val, List.drop_zero, hsorted, sortedMmioPools]
    simpa only [decide_eq_true_eq] using
      (List.pairwise_mergeSort (le := fun a b : AddressRange => decide (a.start.val ≤ b.start.val))
      (by simp only [decide_eq_true_eq]; exact fun _ _ _ => Nat.le_trans)
      (by intro a b; simp only [Bool.or_eq_true, decide_eq_true_eq]; omega) (mmioPoolList self))
  · simpa [alloc.vec.Vec.deref, alloc.vec.Vec.val, hsorted] using hnext


/-- The requested intersections cover exactly the request's addresses that are
    in a configured pool, independently of emptiness representations and order. -/
theorem reservationOverlaps_covers (pools : List AddressRange) (range : AddressRange) (addr : Nat) :
    AddressAllocator.Covers (reservationOverlaps pools range) addr ↔
      AddressAllocator.Covers pools addr ∧ range.containsModel addr := by
  simp only [AddressAllocator.Covers, reservationOverlaps, List.mem_filterMap]
  constructor
  · rintro ⟨overlap, ⟨pool, hp, heq⟩, ha⟩
    split at heq
    · cases heq
    · cases heq
      simp only [intersection, AddressRange.containsModel, val_min, val_max] at ha
      exact ⟨⟨pool, hp, by simp only [AddressRange.containsModel]; omega⟩,
        by simp only [AddressRange.containsModel]; omega⟩
  · rintro ⟨⟨pool, hp, hpool⟩, hrange⟩
    have ha : (intersection pool range).containsModel addr := by
      simp only [intersection, AddressRange.containsModel, val_min, val_max] at *
      omega
    have hn : ¬(intersection pool range).isEmptyModel := by
      simp only [AddressRange.isEmptyModel, AddressRange.containsModel] at *
      omega
    exact ⟨intersection pool range, ⟨pool, hp, by simp [hn]⟩, ha⟩

/-- No component other than MMIO, and no field other than its state and the
    anonymous counter, is changed by a reservation sequence. -/
theorem MmioReservationSequence.frame {self a : SystemAllocator} {overlaps result}
    (h : MmioReservationSequence self overlaps result a) :
    a = { self with next_anon_id := a.next_anon_id, mmio_address_spaces := a.mmio_address_spaces } := by
  induction overlaps generalizing self with
  | nil => obtain ⟨_, rfl⟩ := h; rfl
  | cons overlap rest ih =>
    obtain ⟨first, next, hattempt, hrest⟩ := h
    have hf := hattempt.frame.2
    cases first with
    | Ok u =>
      cases u
      have hr := ih hrest
      conv_lhs => rw [hr, hf]
    | Err error =>
      obtain ⟨_, rfl⟩ := hrest
      exact hf

/-- Success consumes exactly one ID for each nonempty pool intersection. -/
theorem MmioReservationSequence.success_counter {self a : SystemAllocator} {overlaps}
    (h : MmioReservationSequence self overlaps (.Ok ()) a) :
    a.next_anon_id.val = self.next_anon_id.val + overlaps.length := by
  induction overlaps generalizing self with
  | nil => obtain ⟨_, rfl⟩ := h; simp
  | cons overlap rest ih =>
    obtain ⟨first, next, hattempt, hrest⟩ := h
    have hc := hattempt.frame.1
    cases first with
    | Ok u =>
      cases u
      have hr := ih hrest
      simp only [List.length_cons]
      omega
    | Err error => cases hrest.1

/-- An error consumes a nonempty prefix's IDs, including the failed attempt. -/
theorem MmioReservationSequence.error_counter {self a : SystemAllocator} {overlaps error}
    (h : MmioReservationSequence self overlaps (.Err error) a) :
    self.next_anon_id.val < a.next_anon_id.val ∧
      a.next_anon_id.val ≤ self.next_anon_id.val + overlaps.length := by
  induction overlaps generalizing self with
  | nil => cases h.1
  | cons overlap rest ih =>
    obtain ⟨first, next, hattempt, hrest⟩ := h
    have hc := hattempt.frame.1
    cases first with
    | Ok u =>
      cases u
      have hr := ih hrest
      simp only [List.length_cons]
      omega
    | Err e =>
      obtain ⟨_, rfl⟩ := hrest
      simp only [List.length_cons]
      omega

/-- A reservation with no pool intersection succeeds without consuming an ID. -/
theorem MmioReservationOutcome.no_overlap {self a : SystemAllocator} {range result}
    (h : MmioReservationOutcome self range result a)
    (hn : ∀ addr, ¬(AddressAllocator.Covers (mmioPoolList self) addr ∧ range.containsModel addr)) :
    result = .Ok () ∧ a = self := by
  have hempty : reservationOverlaps (sortedMmioPools self) range = [] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro overlap hmem
    simp only [reservationOverlaps, List.mem_filterMap] at hmem
    obtain ⟨pool, hp, heq⟩ := hmem
    split at heq
    · cases heq
    · rename_i hnonempty
      cases heq
      obtain ⟨addr, ha⟩ := AddressRange.not_isEmptyModel_iff_exists_containsModel _ |>.mp hnonempty
      apply hn addr
      have hp' : pool ∈ mmioPoolList self := (List.mergeSort_perm _ _).mem_iff.mp hp
      simp only [intersection, AddressRange.containsModel, val_min, val_max] at ha
      exact ⟨⟨pool, hp', by simp only [AddressRange.containsModel]; omega⟩,
        by simp only [AddressRange.containsModel]; omega⟩
  simpa [MmioReservationOutcome, hempty, MmioReservationSequence] using h


private theorem reservationOverlaps_empty (pools : List AddressRange) (range : AddressRange)
    (hempty : range.isEmptyModel) : reservationOverlaps pools range = [] := by
  simp only [reservationOverlaps, List.filterMap_eq_nil_iff]
  intro pool _
  have he : (intersection pool range).isEmptyModel := by
    simp only [intersection, AddressRange.isEmptyModel, val_min, val_max] at *
    omega
  simp [he]

/-- Every representation of an empty inclusive range is a no-op, even when the
    anonymous counter is exhausted. Only the pool-vector capacity bound is needed. -/
theorem reserve_mmio_empty_spec (self : SystemAllocator) (range : AddressRange)
    (hwf : WellFormed self) (hsize : (mmioPoolList self).length ≤ Usize.max)
    (hempty : range.isEmptyModel) :
    reserve_mmio self range ⦃ result a => result = .Ok () ∧ a = self ⦄ := by
  have hnone := reservationOverlaps_empty (sortedMmioPools self) range hempty
  apply WP.spec_mono (reserve_mmio_spec self range hwf hsize (by simp only [hnone, List.length_nil, Nat.add_zero]; scalar_tac))
  rintro ⟨result, a⟩ ⟨_, hout⟩
  simpa [MmioReservationOutcome, hnone, MmioReservationSequence] using hout

end resources.system_allocator.SystemAllocator
