import MaximalBarrier
import Mathlib.Data.Fintype.Sum

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- The vertices missed by any genuine maximum matching realize the minimum
unmatched count, including on an empty graph. -/
theorem maximum_uncovered_count {X : Type*} [Finite X] {G : SimpleGraph X}
    (M : G.Subgraph) (matching : M.IsMatching) (maximum : M.edgeSet.ncard = matchingEdges G) :
    Nat.card ↥(M.vertsᶜ : Set X) = minUnmatched G := by
  rw [minUnmatched_eq_deficit, ← maximum]
  exact uncovered_eq matching

/-- Once every residual component is odd, an optimal barrier makes their
number exactly the combined number of barrier vertices and missed vertices. -/
theorem barrier_exit_count {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S) (M : G.Subgraph) (matching : M.IsMatching)
    (maximum : M.edgeSet.ncard = matchingEdges G)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp)) :
    Nat.card (G.induce Sᶜ).ConnectedComponent = Nat.card (↥S ⊕ ↥(M.vertsᶜ : Set X)) := by
  let Y := G.induce Sᶜ
  have all : Y.oddComponents = Set.univ :=
    Set.eq_univ_of_forall fun c => (odd c : Odd (Nat.card c.supp))
  change Y.oddComponents.ncard = S.ncard + minUnmatched G at tight
  rw [all,Set.ncard_univ] at tight
  change Nat.card Y.ConnectedComponent = _
  rw [Nat.card_sum,maximum_uncovered_count M matching maximum]
  exact tight

#print axioms maximum_uncovered_count
#print axioms barrier_exit_count
end JSP452Audit.StarHost
