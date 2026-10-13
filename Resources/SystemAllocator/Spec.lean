module
public import Resources.AddressAllocator.Spec
import all Aeneas.Std.VecIter
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
  | some r, some a => AddressAllocator.initialState r a alignment alignment ∧ AddressAllocator.WellFormed a
  | _, _ => False

/-- All component allocators satisfy their structural invariant. -/
def WellFormed (a : SystemAllocator) : Prop :=
  (∀ io ∈ a.io_address_space, AddressAllocator.WellFormed io) ∧
  (∀ mmio ∈ a.mmio_address_spaces.val, AddressAllocator.WellFormed mmio) ∧
  (∀ platform ∈ a.mmio_platform_address_spaces, AddressAllocator.WellFormed platform) ∧
  AddressAllocator.WellFormed a.irq_allocator ∧ AddressAllocator.WellFormed a.gpe_allocator ∧
  ∀ bus space, Finmap.lookup bus a.pci_allocator = some space → AddressAllocator.WellFormed space

/-- Exact initial pools and alignments, with no allocations or PCI buses. -/
def InitialState (config : SystemAllocatorConfig) (ranges : List AddressRange)
    (pageSize : U64) (high : AddressRange) (reserved : Option AddressRange)
    (a : SystemAllocator) : Prop :=
  OptionalInitial config.io 0x400#u64 a.io_address_space ∧
  (∃ lowSpace highSpace, a.mmio_address_spaces.val = [lowSpace, highSpace] ∧
    AddressAllocator.initialStateFromList (mmioPools ranges config.low_mmio) lowSpace pageSize pageSize ∧
    AddressAllocator.initialStateFromList (mmioPools ranges high) highSpace pageSize pageSize) ∧
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
  · refine ⟨?_, ?_, ?_, hwi, hwg, ?_⟩
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

end resources.system_allocator.SystemAllocator
