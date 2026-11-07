import MatchedDeletion
import EdgeDeleteExact

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Charge b genuinely blue neighbors against edge loss minus matching-number loss.
The red graph is exactly the spanning graph of the maximum matching M. -/
theorem blue_matching_charge {X : Type*} [Finite X] (G : SimpleGraph X) (M : G.Subgraph)
    (hM : M.IsMatching) (maxM : M.edgeSet.ncard = matchingEdges G) (v : X) (b : ℕ)
    (hb : b ≤ Nat.card ((G \ M.spanningCoe).neighborSet v)) :
    b + (G.induce {x | x ≠ v}).edgeSet.ncard + matchingEdges G ≤
      G.edgeSet.ncard + matchingEdges (G.induce {x | x ≠ v}) := by
  have sub : (G \ M.spanningCoe).neighborSet v ⊆ G.neighborSet v := fun _ hh => hh.1
  have edges := card_neighbor_add_induce_edge_ncard G v
  by_cases hv : v ∈ M.verts
  · obtain ⟨w, red, _⟩ := hM hv
    have strict : (G \ M.spanningCoe).neighborSet v ⊂ G.neighborSet v :=
      ⟨sub, fun back => (back (M.adj_sub red)).2 red⟩
    have extra : Nat.card ((G \ M.spanningCoe).neighborSet v) < Nat.card (G.neighborSet v) :=
      Set.ncard_lt_ncard strict
    have loss := matchingEdges_le_delete_add_one G v
    omega
  · have same := matchingEdges_delete_eq_of_avoiding G v ⟨M, hM, maxM, hv⟩
    have le : Nat.card ((G \ M.spanningCoe).neighborSet v) ≤ Nat.card (G.neighborSet v) :=
      Set.ncard_le_ncard sub
    omega

#print axioms blue_matching_charge
end JSP452Audit.StarHost
