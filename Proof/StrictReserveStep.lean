import ReserveRowBudget

namespace JSP452Audit.StarHost
open SimpleGraph

/-- At a rank-preserving maximum-degree vertex with zero top budget, at
most min(H,D-1) layers can gain a unit while the deletion removes D edges. -/
theorem reserve_gain_delete_peak {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) (D H : ℕ)
    (pos : 0 < D) (deg : Nat.card (G.neighborSet v) = D)
    (peak : ∀ x, Nat.card (G.neighborSet x) ≤ D) (topZero : deletionBudget G D = 0)
    (same : matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G) :
    baseReserve (G.induce {x | x ≠ v}) H + (D - min H (D-1)) ≤ baseReserve G H := by
  let Y := G.induce {x | x ≠ v}
  have high (j : ℕ) (hj : D-1 < j) : deletionBudget G j ≤ deletionBudget Y j := by
    by_cases eq : j = D
    · rw [eq,topZero]; exact Nat.zero_le _
    · have above : D < j := by omega
      rw [deletionBudget_zero_above G j (by omega) (fun x => lt_of_le_of_lt (peak x) above)]
      exact Nat.zero_le _
  have layers := sum_step_through (deletionBudget G) (deletionBudget Y) (D-1) H
    (fun j _ _ => (deletionBudget_delete_vertex G v j).2) high
  have edges : D + Y.edgeSet.ncard = G.edgeSet.ncard := deg ▸ card_neighbor_add_induce_edge_ncard G v
  have old := base_reserve_account G H
  have new := base_reserve_account Y H
  change matchingEdges Y = matchingEdges G at same
  change baseReserve Y H + (D - min H (D-1)) ≤ baseReserve G H
  omega

/-- At least one unit of reserve is gained at every truncation height. -/
theorem strict_reserve_delete_peak {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) (D H : ℕ)
    (pos : 0 < D) (deg : Nat.card (G.neighborSet v) = D)
    (peak : ∀ x, Nat.card (G.neighborSet x) ≤ D) (topZero : deletionBudget G D = 0)
    (same : matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G) :
    baseReserve (G.induce {x | x ≠ v}) H + 1 ≤ baseReserve G H := by
  have gain := reserve_gain_delete_peak G v D H pos deg peak topZero same
  omega

theorem positive_reserve_of_delete_peak {X : Type*} [Finite X] (G : SimpleGraph X) (v : X) (D H : ℕ)
    (pos : 0 < D) (deg : Nat.card (G.neighborSet v) = D)
    (peak : ∀ x, Nat.card (G.neighborSet x) ≤ D) (topZero : deletionBudget G D = 0)
    (same : matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G) :
    1 ≤ baseReserve G H := by
  have step := strict_reserve_delete_peak G v D H pos deg peak topZero same
  omega

#print axioms reserve_gain_delete_peak
#print axioms strict_reserve_delete_peak
#print axioms positive_reserve_of_delete_peak
end JSP452Audit.StarHost
