module
public import Resources.AddressRangeSpec
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

end resources.address_allocator.AddressAllocator
