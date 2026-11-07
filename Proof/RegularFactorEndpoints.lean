import SelectedDegree
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Each vertex has its unique perfect-matching neighbor on the original vertex type. -/
theorem perfect_spanning_degree {X : Type*} {H : SimpleGraph X}
    (M : H.Subgraph) (perfect : M.IsPerfectMatching) (v : X) :
    Nat.card (M.spanningCoe.neighborSet v) = 1 := by
  obtain ⟨w,hw,uniq⟩ := Subgraph.isPerfectMatching_iff.mp perfect v
  rw [Nat.card_coe_set_eq, Set.ncard_eq_one]
  refine ⟨w,Set.ext fun z => ?_⟩
  exact ⟨fun hz => uniq _ hz,fun hz => (Set.mem_singleton_iff.mp hz).symm ▸ hw⟩

/-- A perfect matching supplies the odd base and permits a parity correction
at the top without passing to a different host. -/
theorem regular_factor_endpoints {X : Type*} [Finite X] (H : SimpleGraph X)
    (D : ℕ) (regular : ∀ v, Nat.card (H.neighborSet v) = D)
    (M : H.Subgraph) (perfect : M.IsPerfectMatching) (p : ℕ) (bound : p ≤ D) :
    ∃ lo j k : ℕ, ∃ L K : SimpleGraph X, p = lo + 2*j ∧ j ≤ k ∧ L ≤ H ∧ K ≤ H ∧
      (∀ v, Nat.card (L.neighborSet v) = lo) ∧
      (∀ v, Nat.card (K.neighborSet v) = lo + 2*k) := by
  let P := M.spanningCoe
  have one (v : X) : Nat.card (P.neighborSet v) = 1 := perfect_spanning_degree M perfect v
  have cut (v : X) : Nat.card ((H \ P).neighborSet v) = D - 1 := by
    have disj : Disjoint P (H \ P) := SimpleGraph.disjoint_left.mpr fun _ _ hp h => h.2 hp
    have all : P ⊔ (H \ P) = H := sup_sdiff_cancel_right M.spanningCoe_le
    have eq := neighbor_card_sup_of_disjoint disj v
    rw [all,regular,one] at eq
    omega
  have base : ∃ L : SimpleGraph X, L ≤ H ∧ ∀ v, Nat.card (L.neighborSet v) = p % 2 := by
    by_cases even : p % 2 = 0
    · exact ⟨⊥,bot_le,fun v => by rw [even,SimpleGraph.neighborSet_bot]; simp⟩
    · exact ⟨P,M.spanningCoe_le,fun v => (one v).trans (by omega)⟩
  let k := (D - p % 2) / 2
  have upper : ∃ K : SimpleGraph X, K ≤ H ∧ ∀ v, Nat.card (K.neighborSet v) = p % 2 + 2*k := by
    by_cases same : D % 2 = p % 2
    · exact ⟨H,le_rfl,fun v => (regular v).trans (by dsimp [k]; omega)⟩
    · exact ⟨H \ P,sdiff_le,fun v => (cut v).trans (by dsimp [k]; omega)⟩
  obtain ⟨L,hL,degL⟩ := base
  obtain ⟨K,hK,degK⟩ := upper
  exact ⟨p%2,p/2,k,L,K,by omega,by dsimp [k]; omega,hL,hK,degL,degK⟩

#print axioms perfect_spanning_degree
#print axioms regular_factor_endpoints
end JSP452Audit.StarHost
