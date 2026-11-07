import Mathlib.Combinatorics.SimpleGraph.Copy
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost

variable {U X : Type*} {A : SimpleGraph U} {R : SimpleGraph X}

/-- Containment supplies an injection on unordered edges, even for graphs
    with isolated vertices. Only the host edge set needs to be finite. -/
theorem edge_ncard_le_of_copy [Finite R.edgeSet] (h : A.IsContained R) :
    A.edgeSet.ncard ≤ R.edgeSet.ncard := by
  obtain ⟨f⟩ := h
  exact Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective

theorem small_edges_exclude_copy [Finite R.edgeSet]
    (small : R.edgeSet.ncard < A.edgeSet.ncard) : ¬ A.IsContained R :=
  fun copy => (Nat.not_le_of_lt small) (edge_ncard_le_of_copy copy)

#print axioms edge_ncard_le_of_copy
#print axioms small_edges_exclude_copy
end JSP452Audit.StarHost
