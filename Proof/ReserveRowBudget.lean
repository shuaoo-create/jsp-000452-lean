import BaseDeletionReserve
import ColumnDeletion
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Nonnegative residual in the base reserve, truncated at the original
finite height ceiling H. -/
noncomputable def baseReserve {X : Type*} [Finite X] (G : SimpleGraph X) (H : ℕ) : ℕ :=
  G.edgeSet.ncard - (matchingEdges G + ∑ i ∈ Finset.range H, deletionBudget G (i+1))

theorem base_reserve_account {X : Type*} [Finite X] (G : SimpleGraph X) (H : ℕ) :
    baseReserve G H + (matchingEdges G + ∑ i ∈ Finset.range H, deletionBudget G (i+1)) =
      G.edgeSet.ncard := Nat.sub_add_cancel (base_deletion_reserve G H)

/-- On the same host the original energy and matching rank receive the extra
base reserve, with no assumption on the sign of the matching deficit. -/
theorem reserve_row_budget {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    rowEnergy n m r + matchingEdges G + baseReserve G (n ⟨0,hs⟩+m ⟨0,ht⟩-2) ≤
      G.edgeSet.ncard + rowCount s t r := by
  have layers := remaining_cost_le_deletions hs ht n m hn hm pn pm G r row
  have reserve := base_reserve_account G (n ⟨0,hs⟩+m ⟨0,ht⟩-2)
  omega
#print axioms base_reserve_account
#print axioms reserve_row_budget
end JSP452Audit.StarHost