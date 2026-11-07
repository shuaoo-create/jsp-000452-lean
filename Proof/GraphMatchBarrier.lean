import HalfCutArithmetic
import TutteJoin

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A finite graph with no matching of k edges has an actual Tutte barrier
    whose removed vertices and component half-orders cost strictly less than k. -/
theorem barrier_of_small_matching {X : Type*} [Finite X] (G : SimpleGraph X) (k : ℕ)
    (low : matchingEdges G < k) :
    ∃ S : Set X, S.ncard + halfComponents (G.induce Sᶜ) < k := by
  classical
  let _ := Fintype.ofFinite X
  by_cases room : 2*k ≤ Nat.card X
  · let d := Nat.card X - 2*k
    let H := tutteJoin G d
    have even : Even (Nat.card X + d) := ⟨Nat.card X-k,by dsimp [d]; omega⟩
    have notPerfect : ¬ ∃ M : H.Subgraph, M.IsPerfectMatching := by
      intro matchH
      have bound := tutteJoin_perfect_le G d matchH
      dsimp [d] at bound
      omega
    have fails := mt H.tutte.mpr notPerfect
    obtain ⟨U,bad⟩ : ∃ U : Set (X ⊕ Fin d), H.IsTutteViolator U := by
      by_contra! no
      exact fails no
    have universals (i : Fin d) (x : X ⊕ Fin d) (neq : x ≠ .inr i) : H.Adj x (.inr i) := by
      cases x with
      | inl a => exact tutteJoin_old_dummy_adj G d a i
      | inr j => exact fun eq => neq (congrArg Sum.inr eq)
    obtain ⟨S,oddCut⟩ := old_odd_cut_of_join_violator G H (tutteJoin_old_adj G d) universals even U bad
    exact ⟨S,half_budget_of_odd_cut G k S room oddCut⟩
  · exact ⟨∅,empty_barrier_small_order G k (by omega)⟩

/-- The non-strict version is convenient for the coloring certificate. -/
theorem barrier_at_matching_number {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ S : Set X, S.ncard + halfComponents (G.induce Sᶜ) ≤ matchingEdges G := by
  obtain ⟨S,h⟩ := barrier_of_small_matching G (matchingEdges G+1) (by omega)
  exact ⟨S,by omega⟩

#print axioms barrier_of_small_matching
#print axioms barrier_at_matching_number
end JSP452Audit.StarHost
