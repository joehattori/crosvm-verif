module
public import VmMemory.MemoryRegion.Spec
@[expose] public section
open Aeneas Aeneas.Std Result

namespace vm_memory.guest_memory.GuestMemory

/-- The regions in slice order. -/
abbrev regionList (self : GuestMemory) : List MemoryRegion := self.regions.val.val

/-- Well-formed guest memory: every region's exclusive end is representable, and
    each region ends at or before every later region starts. -/
def WellFormed (self : GuestMemory) : Prop :=
  (∀ r ∈ self.regionList, r.ValidBounds) ∧ self.regionList.Pairwise MemoryRegion.EndsBefore

/-- Sum of the region lengths, as computed by `memory_size` without overflow. -/
def totalLength (self : GuestMemory) : Nat :=
  (self.regionList.map fun r => r.mapping.length.val).sum

theorem WellFormed.validBounds {self : GuestMemory} (h : self.WellFormed)
    {r : MemoryRegion} (hr : r ∈ self.regionList) : r.ValidBounds :=
  h.1 r hr

/-- Regions are sorted by guest base. -/
theorem WellFormed.sorted {self : GuestMemory} (h : self.WellFormed) :
    self.regionList.Pairwise (fun a b => a.guest_base.val ≤ b.guest_base.val) :=
  h.2.imp fun hab => by unfold MemoryRegion.EndsBefore at hab; omega

/-- At most one region contains a given address. -/
theorem WellFormed.index_eq_of_mem {self : GuestMemory} (h : self.WellFormed)
    {i j : Nat} (hi : i < self.regionList.length) (hj : j < self.regionList.length)
    {addr : Nat}
    (hci : self.regionList[i].guest_base.val ≤ addr ∧
      addr < self.regionList[i].guest_base.val + self.regionList[i].mapping.length.val)
    (hcj : self.regionList[j].guest_base.val ≤ addr ∧
      addr < self.regionList[j].guest_base.val + self.regionList[j].mapping.length.val) :
    i = j := by
  have hp := List.pairwise_iff_getElem.mp h.2
  rcases Nat.lt_trichotomy i j with hij | hij | hij
  · have := hp i j hi hj hij
    unfold MemoryRegion.EndsBefore at this
    omega
  · exact hij
  · have := hp j i hj hi hij
    unfold MemoryRegion.EndsBefore at this
    omega

private theorem start_add_sum_le (l : List MemoryRegion) (hl : l.Pairwise MemoryRegion.EndsBefore)
    (start bound : Nat) (hStart : ∀ r ∈ l, start ≤ r.guest_base.val)
    (hBound : ∀ r ∈ l, r.guest_base.val + r.mapping.length.val ≤ bound)
    (hle : start ≤ bound) :
    start + (l.map fun r => r.mapping.length.val).sum ≤ bound := by
  induction l generalizing start with
  | nil => simpa using hle
  | cons r rs ih =>
    rw [List.pairwise_cons] at hl
    have hr := hStart r (by simp)
    have hrBound := hBound r (by simp)
    have hrs := ih hl.2 (r.guest_base.val + r.mapping.length.val) (fun s hs => hl.1 s hs)
      (fun s hs => hBound s (by simp [hs])) hrBound
    simp only [List.map_cons, List.sum_cons]
    omega

/-- The total length fits in `u64`, so summing region sizes cannot overflow. -/
theorem WellFormed.totalLength_le {self : GuestMemory} (h : self.WellFormed) :
    self.totalLength ≤ U64.max := by
  have := start_add_sum_le self.regionList h.2 0 U64.max (fun _ _ => Nat.zero_le _)
    (fun r hr => h.validBounds hr) (Nat.zero_le _)
  simpa [totalLength] using this

end vm_memory.guest_memory.GuestMemory
