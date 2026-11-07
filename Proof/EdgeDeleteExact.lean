import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost

/-- Separate the edges incident to v from the edges of the graph on the
    remaining vertices. No decidability assumption on adjacency is required. -/
theorem card_neighbor_add_induce_edge_ncard {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) :
    Nat.card (G.neighborSet v) + (G.induce {x | x ≠ v}).edgeSet.ncard = G.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite X
  have restrict : (G.induce {x | x ≠ v}).edgeSet.ncard = (G.deleteIncidenceSet v).edgeSet.ncard := by
    change Nat.card (G.induce {v}ᶜ).edgeSet = Nat.card (G.deleteIncidenceSet v).edgeSet
    simp only [Nat.card_eq_fintype_card, SimpleGraph.card_edgeSet]
    exact G.card_edgeFinset_induce_compl_singleton v
  have incident : Nat.card (G.neighborSet v) = (G.incidenceSet v).ncard :=
    Nat.card_congr (G.incidenceSetEquivNeighborSet v).symm
  rw [incident, restrict, G.edgeSet_deleteIncidenceSet, Nat.add_comm]
  exact Set.ncard_sdiff_add_ncard_of_subset (G.incidenceSet_subset v)

#print axioms card_neighbor_add_induce_edge_ncard
end JSP452Audit.StarHost
