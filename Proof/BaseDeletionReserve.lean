import DeletionStep
import TopBudgetVertex
import BudgetCeiling
import ActualMaximumDegree
import ReserveSumStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The base reserve: all positive deletion costs up to any fixed height and
the original matching number fit inside the original finite edge count. -/
theorem base_deletion_reserve {X : Type u} [Finite X] (G : SimpleGraph X) (H : ℕ) :
    matchingEdges G + ∑ i ∈ Finset.range H, deletionBudget G (i+1) ≤ G.edgeSet.ncard := by
  have go (T : ℕ) : ∀ {Z : Type u} [Finite Z] (Y : SimpleGraph Z), Y.edgeSet.ncard = T →
      matchingEdges Y + ∑ i ∈ Finset.range H, deletionBudget Y (i+1) ≤ Y.edgeSet.ncard := by
    induction T using Nat.strong_induction_on with
    | h T ih =>
      intro Z _ Y count
      rcases all_zero_or_real_peak Y with empty | ⟨x,pos,bound⟩
      · have bot : Y = ⊥ := by
          apply le_antisymm _ bot_le
          intro a b e
          have has := (Set.ncard_pos (Y.neighborSet a).toFinite).mpr (show (Y.neighborSet a).Nonempty from ⟨b,e⟩)
          have zero := empty a
          change 0 < Nat.card (Y.neighborSet a) at has
          omega
        have noEdges := SimpleGraph.edgeSet_eq_empty.mpr bot
        have rank := (deletionBudget_and_rank_edgeless Y noEdges 1 (by decide)).2
        have noCost (i : ℕ) : deletionBudget Y (i+1)=0 := (deletionBudget_and_rank_edgeless Y noEdges _ (by omega)).1
        simp [rank,noCost]
      · let D := Nat.card (Y.neighborSet x)
        have choice : ∃ v, Nat.card (Y.neighborSet v) = D ∧
            (deletionBudget Y D=0 ∨ matchingEdges Y = matchingEdges (Y.induce {z | z≠v})) := by
          by_cases top : deletionBudget Y D=0
          · exact ⟨x,rfl,Or.inl top⟩
          · obtain ⟨v,d,rank⟩ := exists_top_budget_vertex Y D pos bound (Nat.pos_of_ne_zero top)
            exact ⟨v,d,Or.inr rank.symm⟩
        obtain ⟨v,deg,atTop⟩ := choice
        let F := Y.induce {z | z≠v}
        have drop : D + F.edgeSet.ncard = Y.edgeSet.ncard := deg ▸ card_neighbor_add_induce_edge_ncard Y v
        have hD : 0 < D := pos
        have prev := ih F.edgeSet.ncard (by omega) F rfl
        have step := reserve_sum_step (deletionBudget Y) (deletionBudget F) (matchingEdges Y)
          (matchingEdges F) D H hD (matchingEdges_le_delete_add_one Y v)
          (fun j _ _ => (deletionBudget_delete_vertex Y v j).2)
          (fun j hj => by rw [deletionBudget_zero_above Y j (by omega) (fun z => lt_of_le_of_lt (bound z) hj)]; omega)
          atTop
        omega
  exact go _ G rfl
#print axioms base_deletion_reserve
end JSP452Audit.StarHost