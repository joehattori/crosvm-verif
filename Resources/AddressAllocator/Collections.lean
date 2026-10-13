module
public import Resources.AddressRange.Spec
@[expose] public section
open Aeneas Aeneas.Std Result
open resources.address_range

namespace resources.Alloc

/-- The derived Rust key equality agrees with the equality used by Finmap. -/
@[step]
theorem eq_spec (x y : Alloc) :
    Insts.CoreCmpPartialEqAlloc.eq x y ⦃ b => b = true ↔ x = y ⦄ := by
  cases x <;> cases y <;>
    simp [Insts.CoreCmpPartialEqAlloc.eq, read_discriminant, lift]
  all_goals split_ifs <;> simp_all

end resources.Alloc

namespace resources.address_allocator.AddressAllocator

/-- Hash-map iteration contains exactly the map entries, regardless of order. -/
@[step]
theorem hashMap_iter_spec {K V S A : Type} [DecidableEq K]
    (m : _root_.std.collections.hash.map.HashMap K V S A) :
    _root_.std.collections.hash.map.HashMap.iter m ⦃ entries =>
      ∀ key value, (key, value) ∈ entries ↔ Finmap.lookup key m = some value ⦄ := by
  simp only [_root_.std.collections.hash.map.HashMap.iter, WP.spec_ok]
  intro key value
  rw [Finmap.lookup_eq_some_iff]
  simp only [List.mem_map, Multiset.mem_toList]
  constructor
  · rintro ⟨⟨k, v⟩, hm, he⟩
    cases he
    exact hm
  · intro hm
    exact ⟨⟨key, value⟩, hm, rfl⟩

private theorem containsKeyList_spec (keys : List resources.Alloc) (key : resources.Alloc) :
    _root_.std.collections.hash.map.containsKeyList
      (resources.core.borrow.Borrow.Blanket resources.Alloc)
      resources.Alloc.Insts.CoreCmpEq key keys ⦃ b => b = true ↔ key ∈ keys ⦄ := by
  induction keys with
  | nil => simp [_root_.std.collections.hash.map.containsKeyList]
  | cons head tail ih =>
    unfold _root_.std.collections.hash.map.containsKeyList
    simp only [resources.core.borrow.Borrow.Blanket, _root_.core.borrow.Borrow.Blanket.borrow,
      resources.Alloc.Insts.CoreCmpEq, resources.Alloc.Insts.CoreCmpPartialEqAlloc]
    step with resources.Alloc.eq_spec head key as ⟨b, hb⟩
    split
    · simp_all
    · step with ih
      simp_all [eq_comm]

@[step]
theorem contains_key_spec (self : AddressAllocator) (key : resources.Alloc) :
    _root_.std.collections.hash.map.HashMap.contains_key
      resources.Alloc.Insts.CoreCmpEq resources.Alloc.Insts.CoreHashHash
      resources.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (resources.core.borrow.Borrow.Blanket resources.Alloc)
      resources.Alloc.Insts.CoreHashHash resources.Alloc.Insts.CoreCmpEq self.allocs key
      ⦃ b => b = true ↔ key ∈ self.allocs ⦄ := by
  unfold _root_.std.collections.hash.map.HashMap.contains_key
  step with containsKeyList_spec
  simp_all [Finmap.mem_keys]

private theorem findKeyList_spec (keys : List resources.Alloc) (key : resources.Alloc) :
    _root_.std.collections.hash.map.findKeyList
      (resources.core.borrow.Borrow.Blanket resources.Alloc)
      resources.Alloc.Insts.CoreCmpEq key keys ⦃ found =>
        found = if key ∈ keys then some key else none ⦄ := by
  induction keys with
  | nil => simp [_root_.std.collections.hash.map.findKeyList]
  | cons head tail ih =>
    unfold _root_.std.collections.hash.map.findKeyList
    simp only [resources.core.borrow.Borrow.Blanket, _root_.core.borrow.Borrow.Blanket.borrow,
      resources.Alloc.Insts.CoreCmpEq, resources.Alloc.Insts.CoreCmpPartialEqAlloc]
    step with resources.Alloc.eq_spec key head as ⟨same, heq⟩
    split
    · simp_all
    · step with ih
      simp_all

/-- Removing an allocation returns its previous value and erases exactly its key;
    a missing key leaves the map unchanged. -/
@[step]
theorem remove_alloc_spec (self : AddressAllocator) (key : resources.Alloc) :
    _root_.std.collections.hash.map.HashMap.remove
      resources.Alloc.Insts.CoreCmpEq resources.Alloc.Insts.CoreHashHash
      resources.std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher
      (resources.core.borrow.Borrow.Blanket resources.Alloc)
      resources.Alloc.Insts.CoreHashHash resources.Alloc.Insts.CoreCmpEq self.allocs key
      ⦃ found rest => match Finmap.lookup key self.allocs with
        | none => found = none ∧ rest = self.allocs
        | some entry => found = some entry ∧ rest = Finmap.erase key self.allocs ⦄ := by
  unfold _root_.std.collections.hash.map.HashMap.remove
  step with findKeyList_spec self.allocs.keys.toList key as ⟨found, hfound⟩
  simp only [Finset.mem_toList, Finmap.mem_keys] at hfound
  cases hlookup : Finmap.lookup key self.allocs with
  | none =>
    have hmissing := Finmap.lookup_eq_none.mp hlookup
    simp_all
  | some entry =>
    have hpresent := Finmap.mem_of_lookup_eq_some hlookup
    simp_all

/-- Nonempty free ranges, in address order, with no overlaps. -/
def ValidRegions (regions : List AddressRange) : Prop :=
  (∀ r ∈ regions, ¬r.isEmptyModel) ∧
    regions.Pairwise (fun r s => r.end.val < s.start.val)

/-- Disjoint inclusive ranges. -/
abbrev DisjointRanges (r s : AddressRange) : Prop :=
  r.end.val < s.start.val ∨ s.end.val < r.start.val

@[simp] theorem validRegions_nil : ValidRegions [] := by simp [ValidRegions]

@[simp] theorem validRegions_cons (r : AddressRange) (rs : List AddressRange) :
    ValidRegions (r :: rs) ↔ ¬r.isEmptyModel ∧ ValidRegions rs ∧
      ∀ s ∈ rs, r.end.val < s.start.val := by
  simp only [ValidRegions, List.forall_mem_cons, List.pairwise_cons]
  tauto

private theorem removeList_spec (rs : List AddressRange) (key : AddressRange)
    (hv : ValidRegions rs) (hk : ¬key.isEmptyModel) :
    _root_.alloc.collections.btree.set.removeList
      (resources.core.borrow.Borrow.Blanket AddressRange)
      AddressRange.Insts.CoreCmpOrd key rs ⦃ removed rest =>
        (removed = true ↔ key ∈ rs) ∧ ValidRegions rest ∧
          ∀ r, r ∈ rest ↔ r ∈ rs ∧ r ≠ key ⦄ := by
  induction rs with
  | nil => simp [_root_.alloc.collections.btree.set.removeList]
  | cons head tail ih =>
    rcases (validRegions_cons _ _).mp hv with ⟨hh, ht, hsep⟩
    unfold _root_.alloc.collections.btree.set.removeList
    simp only [resources.core.borrow.Borrow.Blanket,
      _root_.core.borrow.Borrow.Blanket.borrow]
    step with AddressRange.cmp_nonempty_spec key head hk hh as ⟨o, heq, hlt, hgt⟩
    split
    · rename_i he
      have hkey := heq.mp he
      subst key
      have hn : head ∉ tail := by
        intro hm
        have := hsep head hm
        simp only [AddressRange.isEmptyModel] at hh
        omega
      simp only [WP.spec_ok]
      refine ⟨by simp, ht, ?_⟩
      intro r
      simp only [List.mem_cons]
      aesop
    · rename_i he
      have hne : key ≠ head := mt heq.mpr he
      step with ih ht as ⟨removed, rest, hremoved, hrest, hmem⟩
      refine ⟨by simpa [List.mem_cons, hne] using hremoved, ?_, ?_⟩
      · apply (validRegions_cons _ _).mpr
        exact ⟨hh, hrest, fun r hr => hsep r ((hmem r).mp hr).1⟩
      · intro r
        simp only [List.mem_cons, hmem]
        aesop

@[step]
theorem remove_region_spec (rs : List AddressRange) (key : AddressRange)
    (hv : ValidRegions rs) (hk : key ∈ rs) :
    _root_.alloc.collections.btree.set.BTreeSet.remove
      resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      (resources.core.borrow.Borrow.Blanket AddressRange)
      AddressRange.Insts.CoreCmpOrd AddressRange.Insts.CoreCmpOrd rs key
      ⦃ removed rest => removed = true ∧ ValidRegions rest ∧
        ∀ r, r ∈ rest ↔ r ∈ rs ∧ r ≠ key ⦄ := by
  unfold _root_.alloc.collections.btree.set.BTreeSet.remove
  step with removeList_spec rs key hv (hv.1 key hk)
  simp_all

private theorem insertList_spec (rs : List AddressRange) (value : AddressRange)
    (hv : ValidRegions rs) (hn : ¬value.isEmptyModel)
    (hd : ∀ r ∈ rs, DisjointRanges value r) :
    _root_.alloc.collections.btree.set.insertList AddressRange.Insts.CoreCmpOrd value rs
      ⦃ added rest => added = true ∧ ValidRegions rest ∧
        ∀ r, r ∈ rest ↔ r = value ∨ r ∈ rs ⦄ := by
  induction rs with
  | nil => simp [_root_.alloc.collections.btree.set.insertList, hn]
  | cons head tail ih =>
    rcases (validRegions_cons _ _).mp hv with ⟨hh, ht, hsep⟩
    have hdh := hd head (by simp)
    have hdt : ∀ r ∈ tail, DisjointRanges value r := fun r hr => hd r (by simp [hr])
    unfold _root_.alloc.collections.btree.set.insertList
    step with AddressRange.cmp_nonempty_spec value head hn hh as ⟨o, heq, hlt, hgt⟩
    cases o with
    | lt =>
      have hb : value.end.val < head.start.val := by
        have := hlt.mp rfl
        simp only [AddressRange.ltModel, DisjointRanges, AddressRange.isEmptyModel] at *
        omega
      simp only [WP.spec_ok]
      refine ⟨rfl, (validRegions_cons _ _).mpr ⟨hn, hv, ?_⟩, ?_⟩
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hr
        · exact hb
        · have := hsep r hr
          simp only [AddressRange.isEmptyModel] at hh
          omega
      · simp
    | eq =>
      have he := heq.mp rfl
      subst value
      simp only [DisjointRanges, AddressRange.isEmptyModel] at hdh hn
      omega
    | gt =>
      have hb : head.end.val < value.start.val := by
        have := hgt.mp rfl
        simp only [AddressRange.ltModel, DisjointRanges, AddressRange.isEmptyModel] at *
        omega
      step with ih ht hdt as ⟨added, rest, ha, hvrest, hmem⟩
      refine ⟨ha, (validRegions_cons _ _).mpr ⟨hh, hvrest, ?_⟩, ?_⟩
      · intro r hr
        rcases (hmem r).mp hr with rfl | hr
        · exact hb
        · exact hsep r hr
      · intro r
        simp only [List.mem_cons, hmem]
        tauto

@[step]
theorem insert_region_spec (rs : List AddressRange) (value : AddressRange)
    (hv : ValidRegions rs) (hn : ¬value.isEmptyModel)
    (hd : ∀ r ∈ rs, DisjointRanges value r) :
    _root_.alloc.collections.btree.set.BTreeSet.insert
      resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      AddressRange.Insts.CoreCmpOrd rs value
      ⦃ added rest => added = true ∧ ValidRegions rest ∧
        ∀ r, r ∈ rest ↔ r = value ∨ r ∈ rs ⦄ := by
  exact insertList_spec rs value hv hn hd

theorem ValidRegions.disjoint {rs : List AddressRange} (hv : ValidRegions rs)
    {r s : AddressRange} (hr : r ∈ rs) (hs : s ∈ rs) (hne : r ≠ s) :
    DisjointRanges r s := by
  induction rs with
  | nil => simp at hr
  | cons head tail ih =>
    rcases (validRegions_cons _ _).mp hv with ⟨hh, ht, hsep⟩
    rcases List.mem_cons.mp hr with rfl | hrt
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact False.elim (hne rfl)
      · exact Or.inl (hsep s hs)
    · rcases List.mem_cons.mp hs with rfl | hs
      · exact Or.inr (hsep r hrt)
      · exact ih ht hrt hs

/-- Insert a remainder only when it is nonempty. This abbreviates the exact
    conditional update in the extracted allocator helper. -/
def insertRemainder (rs : List AddressRange) (r : AddressRange) :
    Result (List AddressRange) := do
  let empty ← AddressRange.is_empty r
  if empty then ok rs
  else
    let (_, rest) ← _root_.alloc.collections.btree.set.BTreeSet.insert
      resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone
      AddressRange.Insts.CoreCmpOrd rs r
    ok rest

@[step]
theorem insertRemainder_spec (rs : List AddressRange) (r : AddressRange)
    (hv : ValidRegions rs)
    (hd : ¬r.isEmptyModel → ∀ s ∈ rs, DisjointRanges r s) :
    insertRemainder rs r ⦃ rest => ValidRegions rest ∧
      ∀ s, s ∈ rest ↔ (s = r ∧ ¬r.isEmptyModel) ∨ s ∈ rs ⦄ := by
  unfold insertRemainder
  step with AddressRange.is_empty_spec r as ⟨empty, he⟩
  split
  · simp_all
  · have hn : ¬r.isEmptyModel := by simp_all
    step with insert_region_spec rs r hv hn (hd hn)
    simp_all

/-- The adjacent entry on one side of the Rust comparator cut at `slot`.
    `lower = true` selects the greatest entry at most `slot`; false selects
    the least entry strictly greater than it. -/
def Neighbor (rs : List AddressRange) (slot : AddressRange) (lower : Bool)
    (found : Option AddressRange) : Prop :=
  let side := fun r => if lower then ¬slot.ltModel r else slot.ltModel r
  match found with
  | none => ∀ r ∈ rs, ¬side r
  | some r => r ∈ rs ∧ side r ∧ ∀ s ∈ rs, side s →
      s = r ∨ (if lower then s.end.val < r.start.val else r.end.val < s.start.val)

/-- The bounded query and extremum used by `insert_at`. -/
def neighbor (rs : List AddressRange) (slot : AddressRange) (lower : Bool) :
    Result (Option AddressRange) := do
  let query := if lower then (.Unbounded, .Included slot) else (.Excluded slot, .Unbounded)
  let entries ← _root_.alloc.collections.btree.set.BTreeSet.range
    resources.alloc.alloc.Global.Insts.CoreAllocAllocatorClone
    AddressRange.Insts.CoreCmpOrd (resources.core.borrow.Borrow.Blanket AddressRange)
    AddressRange.Insts.CoreCmpOrd (resources.PairBoundBound.Insts.CoreOpsRangeRangeBounds AddressRange)
    rs query
  if lower then
    _root_.alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.max
      (resources.Shared0A.Insts.CoreCmpOrd AddressRange.Insts.CoreCmpOrd) entries
  else
    _root_.alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.min
      (resources.Shared0A.Insts.CoreCmpOrd AddressRange.Insts.CoreCmpOrd) entries

private theorem rangeList_sides_spec (rs : List AddressRange) (slot : AddressRange) (lower : Bool)
    (hv : ValidRegions rs) (hn : ¬slot.isEmptyModel) :
    _root_.alloc.collections.btree.set.rangeList
      (resources.core.borrow.Borrow.Blanket AddressRange) AddressRange.Insts.CoreCmpOrd
      (if lower then .Unbounded else .Excluded slot)
      (if lower then .Included slot else .Unbounded) rs ⦃ entries =>
        entries = rs.filter (fun r => decide (if lower then ¬slot.ltModel r else slot.ltModel r)) ⦄ := by
  induction rs with
  | nil => simp [_root_.alloc.collections.btree.set.rangeList]
  | cons head tail ih =>
    have hh := hv.1 head (by simp)
    have ht := ((validRegions_cons _ _).mp hv).2.1
    cases lower <;>
      simp only [Bool.false_eq_true, ↓reduceIte,
        _root_.alloc.collections.btree.set.rangeList, resources.core.borrow.Borrow.Blanket,
        _root_.core.borrow.Borrow.Blanket.borrow, _root_.alloc.collections.btree.set.boundAllows, bind_ok]
    all_goals
      step with AddressRange.cmp_nonempty_spec head slot hh hn as ⟨o, heq, hlt, hgt⟩
      have htail := ih ht
      simp only [Bool.false_eq_true, ↓reduceIte, resources.core.borrow.Borrow.Blanket] at htail
      step with htail as ⟨entries, hentries⟩
      cases o <;> simp_all [List.filter_cons, AddressRange.ltModel] <;> omega

private theorem validRegions_filter (rs : List AddressRange) (p : AddressRange → Bool)
    (hv : ValidRegions rs) : ValidRegions (rs.filter p) :=
  ⟨fun r hr => hv.1 r (List.mem_filter.mp hr).1, hv.2.filter p⟩

private theorem validRegions_head (rs : List AddressRange) (hv : ValidRegions rs) :
    match rs.head? with
    | none => rs = []
    | some r => r ∈ rs ∧ ∀ s ∈ rs, s = r ∨ r.end.val < s.start.val := by
  cases rs with
  | nil => rfl
  | cons r rs =>
    refine ⟨by simp, ?_⟩
    intro s hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact Or.inl rfl
    · exact Or.inr (((validRegions_cons _ _).mp hv).2.2 s hs)

private theorem validRegions_last (rs : List AddressRange) (hv : ValidRegions rs) :
    match rs.getLast? with
    | none => rs = []
    | some r => r ∈ rs ∧ ∀ s ∈ rs, s = r ∨ s.end.val < r.start.val := by
  induction rs with
  | nil => rfl
  | cons head tail ih =>
    cases tail with
    | nil => simp
    | cons x xs =>
      have ht := ((validRegions_cons _ _).mp hv).2.1
      have hsep := ((validRegions_cons _ _).mp hv).2.2
      have h := ih ht
      simp only [List.getLast?_cons_cons]
      cases he : (x :: xs).getLast? with
      | none => simp [he] at h
      | some r =>
        simp only [he] at h ⊢
        refine ⟨by simp [h.1], ?_⟩
        intro s hs
        rcases List.mem_cons.mp hs with rfl | hs
        · exact Or.inr (hsep r h.1)
        · exact h.2 s hs

@[step]
theorem neighbor_spec (rs : List AddressRange) (slot : AddressRange) (lower : Bool)
    (hv : ValidRegions rs) (hn : ¬slot.isEmptyModel) :
    neighbor rs slot lower ⦃ found => Neighbor rs slot lower found ⦄ := by
  have hfilter := rangeList_sides_spec rs slot lower hv hn
  unfold neighbor
  simp only [_root_.alloc.collections.btree.set.BTreeSet.range,
    _root_.PairBoundBound.Insts.CoreOpsRangeRangeBounds.start_bound,
    _root_.PairBoundBound.Insts.CoreOpsRangeRangeBounds.end_bound]
  cases lower <;> simp only [Bool.false_eq_true, ↓reduceIte,
    _root_.alloc.collections.btree.set.checkBounds, bind_ok] at hfilter ⊢
  all_goals
    step with hfilter as ⟨entries, he⟩
    subst entries
    simp only [_root_.alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.min,
      _root_.alloc.collections.btree.set.Range.Insts.CoreIterTraitsIteratorIteratorSharedAT.max, WP.spec_ok]
  · have h := validRegions_head _ (validRegions_filter rs (fun r => decide (slot.ltModel r)) hv)
    cases he : (rs.filter (fun r => decide (slot.ltModel r))).head? with
    | none =>
      simp only [he] at h ⊢
      simpa [Neighbor] using (List.filter_eq_nil_iff.mp h)
    | some r =>
      simp only [he] at h ⊢
      simp only [List.mem_filter, decide_eq_true_eq] at h
      exact ⟨h.1.1, h.1.2, fun s hs hp => h.2 s ⟨hs, hp⟩⟩
  · have h := validRegions_last _ (validRegions_filter rs (fun r => decide (¬slot.ltModel r)) hv)
    cases he : (rs.filter (fun r => decide (¬slot.ltModel r))).getLast? with
    | none =>
      simp only [he] at h ⊢
      simpa [Neighbor] using (List.filter_eq_nil_iff.mp h)
    | some r =>
      simp only [he] at h ⊢
      simp only [List.mem_filter, decide_eq_true_eq] at h
      exact ⟨h.1.1, h.1.2, fun s hs hp => h.2 s ⟨hs, hp⟩⟩

end resources.address_allocator.AddressAllocator
