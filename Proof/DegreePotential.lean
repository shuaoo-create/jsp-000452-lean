import MatchedDeletion
import CenterPeel

namespace JSP452Audit.StarHost
open SimpleGraph

noncomputable def edgePotential {X : Type*} [Finite X] (G : SimpleGraph X) : ℕ :=
  G.edgeSet.ncard - matchingEdges G

theorem matchingEdges_le_edgeCount {X : Type*} [Finite X] (G : SimpleGraph X) :
    matchingEdges G ≤ G.edgeSet.ncard := by
  obtain ⟨M,_,eq⟩ := exists_maximum_matching G
  rw [← eq]
  exact Set.ncard_le_ncard M.edgeSet_subset

theorem potential_plus_matching {X : Type*} [Finite X] (G : SimpleGraph X) :
    edgePotential G + matchingEdges G = G.edgeSet.ncard :=
  Nat.sub_add_cancel (matchingEdges_le_edgeCount G)

/-- Deleting a vertex of degree d costs at least d−1 in the edge-minus-matching potential. -/
theorem degree_potential_charge {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) :
    Nat.card (G.neighborSet v) - 1 + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  have edges := card_neighbor_add_induce_edge_ncard G v
  have matchDrop := matchingEdges_le_delete_add_one G v
  have nonzero_or_fixed : 0 < Nat.card (G.neighborSet v) ∨ matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G := by
    by_cases pos : 0 < Nat.card (G.neighborSet v)
    · exact Or.inl pos
    · right
      obtain ⟨M,hM,mMax⟩ := exists_maximum_matching G
      apply matchingEdges_delete_eq_of_avoiding G v
      refine ⟨M,hM,mMax,?_⟩
      intro used
      obtain ⟨w,adj,_⟩ := hM used
      have inst : Nonempty (G.neighborSet v) := ⟨⟨w,M.adj_sub adj⟩⟩
      exact pos Nat.card_pos
  have after := potential_plus_matching (G.induce {x | x ≠ v})
  have before := potential_plus_matching G
  omega

theorem paid_potential_of_counts {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) (b : ℕ)
    (paid : b + (G.induce {x | x ≠ v}).edgeSet.ncard + matchingEdges G ≤
      G.edgeSet.ncard + matchingEdges (G.induce {x | x ≠ v})) :
    b + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  have after := potential_plus_matching (G.induce {x | x ≠ v})
  have before := potential_plus_matching G
  omega

#print axioms degree_potential_charge
end JSP452Audit.StarHost
