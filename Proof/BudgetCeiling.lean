import DeletionBudget
import DegreePotential

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- If every original degree is below a positive threshold, the empty
deleted set and the empty matching already witness budget zero. -/
theorem deletionBudget_zero_above (G : SimpleGraph X) (j : ℕ) (pos : 0 < j)
    (low : ∀ x, Nat.card (G.neighborSet x) < j) : deletionBudget G j = 0 := by
  let W : Set X := ∅
  let H := G.induce Wᶜ
  have good : admits_matching_remainder H j := by
    refine ⟨⊥,fun _ h => h.elim,?_⟩
    intro x
    rw [Subgraph.spanningCoe_bot,sdiff_bot]
    exact (induced_neighbor_count_le G Wᶜ x).trans (by have := low x.val; omega)
  have le := deletionBudget_le_of_witness G j W good
  simpa [W] using le

/-- Base case on the empty edge graph, valid also on the empty vertex type. -/
theorem deletionBudget_bot (j : ℕ) (pos : 0 < j) :
    deletionBudget (⊥ : SimpleGraph X) j = 0 := by
  apply deletionBudget_zero_above _ j pos
  intro x
  simpa using pos

theorem matchingEdges_bot : matchingEdges (⊥ : SimpleGraph X) = 0 := by
  simpa using matchingEdges_le_edgeCount (⊥ : SimpleGraph X)

theorem deletionBudget_and_rank_edgeless (G : SimpleGraph X) (empty : G.edgeSet = ∅)
    (j : ℕ) (pos : 0 < j) : deletionBudget G j = 0 ∧ matchingEdges G = 0 := by
  have eq : G = ⊥ := by
    ext x y
    change G.Adj x y ↔ False
    rw [← G.mem_edgeSet,empty]
    exact Iff.rfl
  subst G
  exact ⟨deletionBudget_bot j pos,matchingEdges_bot⟩

#print axioms deletionBudget_zero_above
#print axioms deletionBudget_and_rank_edgeless
end JSP452Audit.StarHost
