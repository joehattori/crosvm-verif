module
public import Resources.AddressAllocator.Spec
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
      remaining.start.val = original.start.val + n.val ∧ remaining.end = original.end ∧
      r.start = original.start ∧ r.end.val + 1 = original.start.val + n.val
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

/-- Component invariants together with IRQ/GPE alignment, bounds, and pool containment. -/
def WellFormed (a : SystemAllocator) : Prop :=
  (∀ io ∈ a.io_address_space, AddressAllocator.WellFormed io) ∧
  (∀ mmio ∈ a.mmio_address_spaces.val, AddressAllocator.WellFormed mmio) ∧
  (∀ platform ∈ a.mmio_platform_address_spaces, AddressAllocator.WellFormed platform) ∧
  AddressAllocator.WellFormed a.irq_allocator ∧ AddressAllocator.WellFormed a.gpe_allocator ∧
  (∀ bus space, Finmap.lookup bus a.pci_allocator = some space → AddressAllocator.WellFormed space) ∧
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

/-- Constructor errors in source evaluation order. Arithmetic failure is excluded
    by the theorem's explicit reservation bounds. The fixed I/O, IRQ, and GPE
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

/-- Total correctness of construction, assuming a successful host page-size query
    and disjoint MMIO restrictions. Invalid configurations return the specified error. -/
@[step]
theorem new_spec (config : SystemAllocatorConfig) (reserve : Option U64)
    (ranges : Slice AddressRange) (hostPageSize : Usize)
    (hpage : _root_.base.sys.unix.system_info.pagesize = ok hostPageSize)
    (hd : AddressAllocator.DisjointPools ranges.val)
    -- TODO(BUG-003): Remove these bounds after fixing the unchecked reservation
    -- arithmetic in SystemAllocator::new and regenerating Lean.
    (hreserve : ∀ n, reserve = some n → config.high_mmio.lenModel ≤ U64.max →
      n.val ≤ config.high_mmio.lenModel →
      0 < config.high_mmio.start.val + n.val ∧
        config.high_mmio.start.val + n.val ≤ U64.max) :
    SystemAllocator.new config reserve ranges ⦃ result =>
      NewOutcome config reserve ranges.val (UScalar.cast .U64 hostPageSize) result ⦄ := by
  unfold SystemAllocator.new
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
        have hbounds := hreserve n rfl hlen hfits'
        step as ⟨upper, hupper⟩
        step as ⟨last, hlast⟩
        step as ⟨start, hstart⟩
        have hr : Reservation config.high_mmio (some n)
            { config.high_mmio with start := start } (some { config.high_mmio with «end» := last }) := by
          refine ⟨?_, rfl, rfl, ?_⟩ <;> simp only <;> omega
        have he : newError config (some n) (UScalar.cast .U64 hostPageSize) =
            newError config none (UScalar.cast .U64 hostPageSize) := by
          simp [newError, Nat.not_lt_of_ge hlen, Nat.not_lt_of_ge hfits']
        have h := afterReservation_outcome config (some n) ranges (UScalar.cast .U64 hostPageSize)
          _ _ hd hr he
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
      AddressAllocator.AlignedAllocationOutcome self.irq_allocator 1#u64
        (.Anon a.next_anon_id) "irq-auto" 1 false (.Err error) a.irq_allocator
  | some irq =>
      AddressAllocator.AlignedAllocationOutcome self.irq_allocator 1#u64
        (.Anon a.next_anon_id) "irq-auto" 1 false (.Ok (UScalar.cast .U64 irq)) a.irq_allocator

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

private theorem unit_placement_iff (rs : List AddressRange) (addr : Nat) :
    AddressAllocator.Placement rs 1 1 addr ↔ AddressAllocator.Covers rs addr := by
  simp [AddressAllocator.Placement, AddressAllocator.Covers, AddressRange.containsModel, Nat.mod_one]

private theorem u32_into_u64 (value : U32) :
    core.convert.num.FromU64U32.from value = UScalar.cast .U64 value := by
  apply UScalar.eq_of_val_eq
  simp

private theorem allocate_unit_spec (self : AddressAllocator) (allocation : resources.Alloc)
    (tag : String) (limit : Nat) (hwf : AddressAllocator.WellFormed self)
    (hunit : UnitAllocatorInvariant limit self) :
    AddressAllocator.allocate self 1#u64 allocation tag ⦃ result a =>
      AddressAllocator.WellFormed a ∧ UnitAllocatorInvariant limit a ∧
      AddressAllocator.AlignedAllocationOutcome self 1#u64 allocation tag 1 false result a ⦄ := by
  apply WP.spec_mono (AddressAllocator.allocate_spec self 1#u64 allocation tag hwf)
  rintro ⟨result, a⟩ h
  have hout : AddressAllocator.AlignedAllocationOutcome self 1#u64 allocation tag 1 false result a := by
    simpa [hunit.1, hunit.2.1] using h.2
  refine ⟨h.1, ?_, hout⟩
  by_cases hk : allocation ∈ self.allocs
  · have hs : a = self := by
      simp [AddressAllocator.AlignedAllocationOutcome, hk] at hout
      exact hout.2
    simpa [hs] using hunit
  · simp only [AddressAllocator.AlignedAllocationOutcome, if_neg hk] at hout
    simp [show Nat.isPowerOfTwo 1 from by decide] at hout
    cases result with
    | Err error => simpa [hout.2.1] using hunit
    | Ok start =>
      obtain ⟨range, _, _, hpools, hmin, hpref, _⟩ := hout.2
      exact hunit.preserved hpools hmin hpref

private theorem allocated_start_u32 {self a : AddressAllocator} {allocation : resources.Alloc}
    {tag : String} {start : U64} {limit : Nat} (hwf : AddressAllocator.WellFormed self)
    (hunit : UnitAllocatorInvariant limit self)
    (hlimit : limit ≤ U32.max)
    (hout : AddressAllocator.AlignedAllocationOutcome self 1#u64 allocation tag 1 false (.Ok start) a) :
    UScalar.cast .U64 (UScalar.cast .U32 start) = start := by
  have hs : AddressAllocator.AlignedAllocation self 1#u64 allocation tag 1 false start a := by
    unfold AddressAllocator.AlignedAllocationOutcome at hout
    split at hout
    · simp at hout
    · simpa [show Nat.isPowerOfTwo 1 from by decide] using hout
  have hbound := hunit.free_le hwf ((unit_placement_iff _ _).mp hs.1.1)
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

private theorem irq_release_invariant {self a : AddressAllocator} {allocation : resources.Alloc}
    {result : core.result.Result AddressRange resources.Error} (hirq : IrqInvariant self)
    (hout : AddressAllocator.ReleaseOutcome self allocation result a) : IrqInvariant a := by
  cases hlookup : Finmap.lookup allocation self.allocs with
  | none =>
    simp only [AddressAllocator.ReleaseOutcome, hlookup] at hout
    simpa [hout.2] using hirq
  | some entry =>
    rcases entry with ⟨range, tag⟩
    simp only [AddressAllocator.ReleaseOutcome, hlookup] at hout
    exact hirq.preserved hout.1 hout.2.1 hout.2.2.1

/-- Release preserves system invariants and changes only the IRQ allocator.
    A missing allocation is a no-op; any release error is discarded. -/
@[step]
theorem release_irq_spec (self : SystemAllocator) (irq : U32) (hwf : WellFormed self) :
    release_irq self irq ⦃ a => WellFormed a ∧ IrqReleaseOutcome self irq a ⦄ := by
  unfold release_irq
  simp only [core.convert.IntoFrom.into, bind_ok, u32_into_u64]
  step with AddressAllocator.release_containing_spec self.irq_allocator (UScalar.cast .U64 irq)
    hwf.2.2.2.1 as ⟨result, irqSpace, hwfi, hout⟩
  have hirqi : IrqInvariant irqSpace := by
    rcases hout with hmissing | ⟨allocation, range, tag, hlookup, hrange, hrelease⟩
    · simpa [hmissing.2.1] using hwf.2.2.2.2.2.2.1
    · exact irq_release_invariant hwf.2.2.2.2.2.2.1 hrelease
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
  unfold AddressAllocator.AllocationAtOutcome at hout
  split at hout
  · simpa [hout.2] using hirq
  · split at hout
    · simpa [hout.2] using hirq
    · cases result with
      | Err error => simpa [hout.1] using hirq
      | Ok u =>
        cases u
        exact hirq.preserved hout.2.1 hout.2.2.1 hout.2.2.2.1

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
      AddressAllocator.AlignedAllocationOutcome self.gpe_allocator 1#u64
        (.Anon a.next_anon_id) "gpe-auto" 1 false (.Err error) a.gpe_allocator
  | some gpe =>
      AddressAllocator.AlignedAllocationOutcome self.gpe_allocator 1#u64
        (.Anon a.next_anon_id) "gpe-auto" 1 false (.Ok (UScalar.cast .U64 gpe)) a.gpe_allocator

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

end resources.system_allocator.SystemAllocator
