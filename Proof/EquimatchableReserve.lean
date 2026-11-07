import RegularIndependentReserve
import MaximalUncovered

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]

/-- The shortfall of every inclusion-maximal matching is paid for by the
reserve. This quantifies the equimatchability conclusion. -/
theorem maximal_shortfall_le_reserve (Q : SimpleGraph X) (d : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=d+1) (crit : PerfectAfterEveryDeletion Q)
    (M : Q.Subgraph) (hm : M.IsMatching)
    (maximal : ∀ N : Q.Subgraph, N.IsMatching → M ≤ N → M=N) :
    matchingEdges Q ≤ baseReserve Q (d+1) + M.edgeSet.ncard := by
  have order := factorCritical_order_rank Q crit (Classical.choice ‹Nonempty X›)
  have count := matching_vertices_eq_twice_edges hm
  have bound := le_matchingEdges hm
  have size := Set.ncard_compl M.verts
  have ne : M.vertsᶜ.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have ind := (maximal_matching_iff_uncovered_independent Q M hm).mp maximal
  have bal := regular_independent_reserve Q d reg crit M.vertsᶜ ne ind
  dsimp only at bal
  rw [compl_compl, matchingEdges_on_matched_verts Q M hm] at bal
  omega

theorem zero_reserve_all_maximal_maximum (Q : SimpleGraph X) (d : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=d+1) (crit : PerfectAfterEveryDeletion Q)
    (zero : baseReserve Q (d+1)=0) (M : Q.Subgraph) (hm : M.IsMatching)
    (maximal : ∀ N : Q.Subgraph, N.IsMatching → M ≤ N → M=N) :
    M.edgeSet.ncard=matchingEdges Q := by
  have bound := maximal_shortfall_le_reserve Q d reg crit M hm maximal
  rw [zero,zero_add] at bound
  exact le_antisymm (le_matchingEdges hm) bound

#print axioms factorCritical_order_rank
#print axioms maximal_shortfall_le_reserve
#print axioms zero_reserve_all_maximal_maximum
end JSP452Audit.StarHost
