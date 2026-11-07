import PartitionHandshake
import RegionDegreeSum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Splitting the vertex set preserves the full handshake sum. -/
theorem degree_sum_complement (G : SimpleGraph X) (U : Set X) :
    originalDegreeSum G U + originalDegreeSum G Uᶜ = 2 * G.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite X
  unfold originalDegreeSum
  rw [Set.Finite.toFinset_compl U.toFinite,Finset.sum_add_sum_compl]
  calc
    ∑ v, Nat.card (G.neighborSet v) = ∑ v, G.degree v :=
      Finset.sum_congr rfl (fun v _ => by rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree])
    _ = 2 * G.edgeSet.ncard := by
      rw [G.sum_degrees_eq_twice_card_edges,← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.card_edgeSet]

private theorem two_block_handshake (G : SimpleGraph X) (U : Set X) :
    originalDegreeSum G U = 2 * (G.induce U).edgeSet.ncard + crossCount G U Uᶜ := by
  have h := partition_handshake G U Uᶜ ∅ disjoint_compl_right (by simp) (by simp)
    (by simp)
  have empty : crossCount G U ∅ = 0 := crossCount_of_no_edges G U ∅ (fun _ _ _ h => h.elim)
  simpa only [empty,Nat.add_zero] using h

/-- Edges deleted with U are its original degree sum corrected for the internal
edges, each of which appeared twice in that sum. -/
theorem root_deletion_cost (G : SimpleGraph X) (U : Set X) :
    G.edgeSet.ncard + (G.induce U).edgeSet.ncard =
      (G.induce Uᶜ).edgeSet.ncard + originalDegreeSum G U := by
  have full := degree_sum_complement G U
  have left := two_block_handshake G U
  have right := two_block_handshake G Uᶜ
  rw [compl_compl,crossCount_swap G Uᶜ U] at right
  omega

/-- With zeta the actual degree shortfall and epsilon the number of internal
edges, the root-deletion cost is the budget D * |U| minus zeta and epsilon. -/
theorem root_deletion_cost_with_slack (G : SimpleGraph X) (U : Set X) (D : ℕ)
    (bound : ∀ v ∈ U, Nat.card (G.neighborSet v) ≤ D) :
    G.edgeSet.ncard + (D * U.ncard - originalDegreeSum G U) + (G.induce U).edgeSet.ncard =
      (G.induce Uᶜ).edgeSet.ncard + D * U.ncard := by
  have budget := degree_sum_le_cap G U D bound
  have cost := root_deletion_cost G U
  omega

#print axioms degree_sum_complement
#print axioms root_deletion_cost
#print axioms root_deletion_cost_with_slack
end JSP452Audit.StarHost
