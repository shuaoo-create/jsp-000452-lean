import AdaptedPortEdgesAndLocalRank
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

abbrev allReserved := R.reserved 0 ∪ R.reserved 1
abbrev adapted := R.portPart 0 ⊔ R.portPart 1
abbrev erased := G \ R.adapted

theorem adapted_adj (x y : X) : R.adapted.Adj x y ↔
    G.Adj x y ∧ (x∈R.allReserved ∨ y∈R.allReserved) := by
  change ((G.Adj x y ∧ (x∈R.reserved 0 ∨ y∈R.reserved 0)) ∨
    (G.Adj x y ∧ (x∈R.reserved 1 ∨ y∈R.reserved 1))) ↔
      G.Adj x y ∧ ((x∈R.reserved 0 ∨ x∈R.reserved 1) ∨ (y∈R.reserved 0 ∨ y∈R.reserved 1))
  tauto

theorem adapted_le : R.adapted≤G := fun x y h => ((R.adapted_adj x y).mp h).1

theorem erased_exact_support : R.erased=portInside G R.allReservedᶜ := by
  ext x y
  change (G.Adj x y ∧ ¬R.adapted.Adj x y) ↔ _
  rw [R.adapted_adj,portInside_adj]
  change _ ↔ G.Adj x y ∧ x∉R.allReserved ∧ y∉R.allReserved
  tauto

theorem exact_port_partition :
    matchingEdges R.adapted=R.totalCapacity ∧
    matchingEdges R.erased+R.totalCapacity=matchingEdges G ∧
    matchingEdges (G.induce R.allReserved)=R.totalCapacity := by
  have hi := rank_of_two_edge_colours R.adapted (R.portPart 0) (R.portPart 1) le_rfl
  rw [R.portPart_rank 0,R.portPart_rank 1] at hi
  change matchingEdges R.adapted≤R.totalCapacity at hi
  have away := R.disjoint_boxes.mono (R.reserved_subset 0) (R.reserved_subset 1)
  have low := disjoint_induced_matching_ranks G R.allReserved (R.reserved 0) (R.reserved 1)
    Set.subset_union_left Set.subset_union_right away
  rw [R.reserved_rank 0,R.reserved_rank 1] at low
  change R.totalCapacity≤matchingEdges (G.induce R.allReserved) at low
  have exterior : matchingEdges R.erased=matchingEdges (G.induce R.allReservedᶜ) := by
    rw [R.erased_exact_support,rank_of_internal_edges]
  have glued := disjoint_induced_matching_ranks G Set.univ R.allReserved R.allReservedᶜ
    (Set.subset_univ _) (Set.subset_univ _) disjoint_compl_right
  rw [rank_eq_of_graph_iso (induceUnivIso G),←exterior] at glued
  have split := rank_of_two_edge_colours G R.adapted R.erased (by
    intro x y e
    by_cases h : R.adapted.Adj x y
    · exact Or.inl h
    · exact Or.inr ⟨e,h⟩)
  omega

#print axioms adapted_adj
#print axioms adapted_le
#print axioms erased_exact_support
#print axioms exact_port_partition
end JSP452Audit.StarHost.NinePortRegion
