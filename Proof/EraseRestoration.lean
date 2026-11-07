import Mathlib.Combinatorics.SimpleGraph.Subgraph
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} {G : SimpleGraph X}

/-- Put every edge of the removed subgraph back in the red class. -/
theorem restoreMatching_red_le (M : G.Subgraph) {R : SimpleGraph X}
    (hR : R ≤ G \ M.spanningCoe) : R ⊔ M.spanningCoe ≤ G :=
  sup_le (hR.trans sdiff_le) M.spanningCoe_le

/-- The blue complement after restoration is exactly the old blue class. -/
theorem restoreMatching_blue_eq (M : G.Subgraph) (R : SimpleGraph X) :
    G \ (R ⊔ M.spanningCoe) = (G \ M.spanningCoe) \ R := by
  ext x y
  simp only [sdiff_adj, sup_adj]
  tauto

/-- Every removed undirected edge is counted once. -/
theorem eraseMatching_edge_count [Finite X] (M : G.Subgraph) :
    (G \ M.spanningCoe).edgeSet.ncard + M.edgeSet.ncard = G.edgeSet.ncard := by
  rw [edgeSet_sdiff, ← M.edgeSet_spanningCoe]
  exact Set.ncard_sdiff_add_ncard_of_subset (edgeSet_subset_edgeSet.mpr M.spanningCoe_le)

#print axioms restoreMatching_red_le
#print axioms restoreMatching_blue_eq
#print axioms eraseMatching_edge_count

end JSP452Audit.StarHost
