import IndependentRegularTop

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- A set paid for by two labels per index has size at most twice the
number of indices, even when labels coincide. -/
theorem ncard_le_twice_of_subset_two_ranges {J : Type*} [Finite J] (K : Set X) (b z : J → X)
    (incl : K ⊆ Set.range b ∪ Set.range z) : K.ncard ≤ 2 * Nat.card J := by
  have size (f : J → X) : (Set.range f).ncard ≤ Nat.card J := by
    simpa using (Set.ncard_image_le (s := (Set.univ : Set J)) (f := f))
  have sub := Set.ncard_le_ncard incl
  have union := Set.ncard_union_le (Set.range b) (Set.range z)
  have hb := size b
  have hz := size z
  omega

/-- If all the surviving covered vertices have been re-matched, the lost
rank is paid for by half the covered labels in the cut. Removing all exposed
full vertices also leaves a degree-D matching cover of deletion cost zero. -/
theorem repair_cut_costs [Finite X] (G : SimpleGraph X) (D : ℕ) (pos : 0 < D)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (M : G.Subgraph) (hm : M.IsMatching) (max : M.edgeSet.ncard = matchingEdges G)
    (I : Set X) (allExposed : exposedFull G M D ⊆ I)
    (N : (G.induce Iᶜ).Subgraph) (hN : N.IsMatching)
    (survives : ∀ x : ↥Iᶜ, x.val ∈ M.verts → x ∈ N.verts)
    (m : ℕ) (paid : (M.verts ∩ I).ncard ≤ 2*m) :
    matchingEdges G ≤ matchingEdges (G.induce Iᶜ) + m ∧
      deletionBudget (G.induce Iᶜ) D = 0 := by
  constructor
  · have left : M.verts \ I ⊆ Subtype.val '' N.verts := by
      rintro x ⟨hx,away⟩
      exact ⟨⟨x,away⟩,survives ⟨x,away⟩ hx,rfl⟩
    have keep := Set.ncard_le_ncard left
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at keep
    have split := Set.ncard_inter_add_ncard_sdiff_eq_ncard M.verts I
    have old := matching_vertices_eq_twice_edges hm
    have new := matching_vertices_eq_twice_edges hN
    have rank := le_matchingEdges hN
    omega
  · let H := G.induce Iᶜ
    have capH (x : ↥Iᶜ) : Nat.card (H.neighborSet x) ≤ D :=
      (induced_neighbor_count_le G Iᶜ x).trans (cap x.val)
    have covers (x : ↥Iᶜ) (high : Nat.card (H.neighborSet x) = D) : x ∈ N.verts := by
      apply survives x
      by_contra miss
      have lower := induced_neighbor_count_le G Iᶜ x
      have original : Nat.card (G.neighborSet x.val) = D := (cap x.val).antisymm (high ▸ lower)
      exact x.property (allExposed ⟨miss,original⟩)
    have good := admits_remainder_of_full_cover H D pos capH N hN covers
    have empty : admits_matching_remainder (H.induce (∅ : Set ↥Iᶜ)ᶜ) D := by
      rw [Set.compl_empty]
      exact admits_remainder_of_induced_embedding (induceUnivIso H).toEmbedding good
    have upper := deletionBudget_le_of_witness H D ∅ empty
    simpa only [Set.ncard_empty, Nat.le_zero] using upper

#print axioms ncard_le_twice_of_subset_two_ranges
#print axioms repair_cut_costs
end JSP452Audit.StarHost
