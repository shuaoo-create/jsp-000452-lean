import HallNeighborhoods

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Split T exactly into the components occupied by its root preimage and
the components missed by the allocation. Injectivity forbids repeated charges. -/
theorem root_allocation_split (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    T.ncard = ({a : S | A.place a ∈ T} : Set S).ncard + (T \ Set.range A.place).ncard := by
  let used := T ∩ Set.range A.place
  let pre := {a : S | A.place a ∈ T}
  have image : A.place '' pre = used := by
    ext c
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨ha,⟨a,rfl⟩⟩
    · rintro ⟨hc,⟨a,rfl⟩⟩
      exact ⟨a,hc,rfl⟩
  have usedCard : used.ncard = pre.ncard := by
    rw [← image,Set.ncard_image_of_injective _ A.place.injective]
  have add := Set.ncard_sdiff_add_ncard_of_subset (show used ⊆ T from Set.inter_subset_left)
  have rest : T \ used = T \ Set.range A.place := by ext; simp [used]
  rw [rest,usedCard] at add
  exact add.symm.trans (Nat.add_comm _ _)

omit [Finite X] in
/-- Every root whose assigned component lies in T truly neighbors T in G. -/
theorem root_preimage_subset_neighbors (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    ({a : S | A.place a ∈ T} : Set S) ⊆ rootNeighbors (rootIncidence G S) T :=
  fun a ha => ⟨A.place a,ha,A.link a⟩

/-- The assigned members of T are reached by distinct neighboring roots. -/
theorem root_deficit_bound (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    T.ncard ≤ (rootNeighbors (rootIncidence G S) T).ncard + (T \ Set.range A.place).ncard := by
  rw [root_allocation_split G S A T]
  exact Nat.add_le_add_right (Set.ncard_le_ncard (root_preimage_subset_neighbors G S A T)) _

/-- When all vertices of each component of T have degree D, every unassigned
member is one of the allocation's full components. -/
theorem root_deficit_bound_full (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (full : T ⊆ {c | allFullComponent G S D c}) :
    T.ncard ≤ (rootNeighbors (rootIncidence G S) T).ncard + (freeFull G S D A).ncard := by
  apply (root_deficit_bound G S A T).trans
  apply Nat.add_le_add_left
  exact Set.ncard_le_ncard (fun _ h => ⟨h.2, full h.1⟩)

/-- For arbitrary T the number of available unassigned components is the
total component count minus the number of roots, with each root used once. -/
theorem root_deficit_bound_all (G : SimpleGraph X) (S : Set X) (A : RootAllocation G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) :
    T.ncard ≤ (rootNeighbors (rootIncidence G S) T).ncard +
      (Nat.card (G.induce Sᶜ).ConnectedComponent - S.ncard) := by
  have free : (T \ Set.range A.place).ncard ≤ (Set.range A.place)ᶜ.ncard :=
    Set.ncard_le_ncard (fun _ h => h.2)
  rw [Set.ncard_compl,Set.ncard_range_of_injective A.place.injective] at free
  exact (root_deficit_bound G S A T).trans (Nat.add_le_add_left free _)

#print axioms root_allocation_split
#print axioms root_preimage_subset_neighbors
#print axioms root_deficit_bound
#print axioms root_deficit_bound_full
#print axioms root_deficit_bound_all
end JSP452Audit.StarHost
