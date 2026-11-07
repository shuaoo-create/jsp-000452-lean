import CoverDegreeSplit
import StarMatchingColor

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- The actual matching covers every height-j vertex. Outside it, all edges
remain, so the degree there is already at most j−1. -/
theorem cover_of_matching_remainder (H : SimpleGraph X) (M : H.Subgraph) (hM : M.IsMatching)
    (j : ℕ) (pos : 0 < j)
    (remainder : ∀ v, Nat.card ((H \ M.spanningCoe).neighborSet v) ≤ j-1) :
    (∀ v, Nat.card (H.neighborSet v) ≤ j) ∧
    (∀ v, Nat.card (H.neighborSet v) = j → v ∈ M.verts) := by
  have subtract (v : X) : Nat.card ((H \ M.spanningCoe).neighborSet v) =
      Nat.card (H.neighborSet v) - Nat.card (M.spanningCoe.neighborSet v) := by
    simp only [Nat.card_coe_set_eq,SimpleGraph.neighborSet_sdiff]
    exact Set.ncard_sdiff (fun _ hv => M.adj_sub hv)
  constructor
  · intro v
    have r := remainder v
    rw [subtract] at r
    have m := spanningMatching_degree_le_one M hM v
    omega
  · intro v height
    have r := remainder v
    rw [subtract,height] at r
    have nonzero : 0 < (M.spanningCoe.neighborSet v).ncard := by
      rw [← Nat.card_coe_set_eq]; omega
    obtain ⟨w,edge⟩ := (Set.ncard_pos (s := M.spanningCoe.neighborSet v)).mp nonzero
    exact M.edge_vert edge

theorem degree_split_of_matching_remainder (H : SimpleGraph X) (M : H.Subgraph)
    (hM : M.IsMatching) (j p q : ℕ) (height : j = p+q) (pos : 0 < j)
    (remainder : ∀ v, Nat.card ((H \ M.spanningCoe).neighborSet v) ≤ j-1) :
    ∃ R : SimpleGraph X, R ≤ H ∧ ∀ v, Nat.card (R.neighborSet v) ≤ p ∧
      Nat.card ((H \ R).neighborSet v) ≤ q := by
  obtain ⟨bound,covers⟩ := cover_of_matching_remainder H M hM j pos remainder
  subst j
  exact degree_split_from_cover H p q bound ⟨M,hM,covers⟩

theorem degree_split_of_exists_matching_remainder (H : SimpleGraph X) (j p q : ℕ)
    (height : j = p+q) (pos : 0 < j)
    (certificate : ∃ M : H.Subgraph, M.IsMatching ∧
      ∀ v, Nat.card ((H \ M.spanningCoe).neighborSet v) ≤ j-1) :
    ∃ R : SimpleGraph X, R ≤ H ∧ ∀ v, Nat.card (R.neighborSet v) ≤ p ∧
      Nat.card ((H \ R).neighborSet v) ≤ q := by
  obtain ⟨M,hM,rest⟩ := certificate
  exact degree_split_of_matching_remainder H M hM j p q height pos rest

#print axioms cover_of_matching_remainder
#print axioms degree_split_of_matching_remainder
#print axioms degree_split_of_exists_matching_remainder
end JSP452Audit.StarHost
