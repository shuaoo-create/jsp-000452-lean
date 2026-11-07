import ArbitraryOddClique
import SmallIndependencePositive
import ReserveTruncation
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]
/-- All regular factor-critical graphs with independence number at most two
pay for their actual unmatched full-degree vertex at every truncation. -/
theorem small_alpha_component_pays (Q : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (small : NoIndependentTriple Q) : minimumExposure Q D ≤ envelopeReserve Q k := by
  classical
  let v : X := Classical.choice ‹Nonempty X›
  rw [regular_factorCritical_exposure Q crit v D reg]
  apply le_trans _ (envelopeReserve_le_truncation Q D k (fun x => (reg x).le))
  by_cases complete : Q=⊤
  · have order := factorCritical_order_rank Q crit v
    let _ := Fintype.ofFinite X
    have bound := Q.degree_lt_card_verts v
    rw [← Q.card_neighborSet_eq_degree,← Nat.card_eq_fintype_card,
      ← Nat.card_eq_fintype_card,reg] at bound
    have two : 2≤matchingEdges Q := by omega
    have pos : D-1+1=D := by omega
    have exactCost := odd_clique_reserve_of_order (X:=X) (matchingEdges Q) (D-1) order two
    rwa [pos,←complete] at exactCost
  · exact (small_independence_noncomplete_reserve Q D large reg crit small complete).trans
      (envelope_reserve_account Q D).2

#print axioms small_alpha_component_pays
end JSP452Audit.StarHost
