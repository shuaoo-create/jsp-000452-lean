import DeletionBudget
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Positive deletion budget at the actual degree ceiling forces a degree-k
vertex outside an attained maximum matching. Deleting it preserves the rank. -/
theorem exists_top_budget_vertex {X : Type*} [Finite X] (G : SimpleGraph X) (k : ℕ)
    (pos : 0 < k) (bound : ∀ x, Nat.card (G.neighborSet x) ≤ k)
    (active : 0 < deletionBudget G k) :
    ∃ v, Nat.card (G.neighborSet v) = k ∧
      matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G := by
  have budgetBound := deletionBudget_le_minimumExposure G k pos bound
  obtain ⟨M,hm,maximum,exposure⟩ := minimumExposure_attained G k
  have positive : 0 < (exposedFull G M k).ncard := active.trans_le (budgetBound.trans_eq exposure.symm)
  obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero positive.ne'
  exact ⟨v,hv.2,matchingEdges_delete_eq_of_avoiding G v ⟨M,hm,maximum,hv.1⟩⟩

#print axioms exists_top_budget_vertex
end JSP452Audit.StarHost
