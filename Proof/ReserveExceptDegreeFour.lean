import LargeExceptionalDeletion
import ActualRowReservePrices
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem exceptional_large_clique_positive [Nonempty X] (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A:Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (four : 4≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) (s : HeavyCliqueFrame Q I D) : 1≤baseReserve Q D := by
  by_contra! fail
  have zero : baseReserve Q D=0 := by omega
  obtain ⟨U,paid,wit⟩ := large_exceptional_deletion Q I ind largest D four par reg crit zero s
  have present := (Set.ncard_pos (Set.toFinite I)).mp (show 0<I.ncard by omega)
  have eq := ((zero_reserve_independent_cut Q D (by omega) reg crit zero I present ind).2.2
    (D-1) (by omega) (by omega)).2
  have bound := deletionBudget_le_of_witness Q (D-1) U wit
  omega

/-- All possible exceptional and nonexceptional decompositions in the
large-degree regular factor-critical obstruction have now been paid. -/
theorem regular_large_degree_envelope [Nonempty X] (Q : SimpleGraph X) (D k : ℕ)
    (six : 6≤D) (conn : Q.Connected) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (crit : PerfectAfterEveryDeletion Q) : minimumExposure Q D≤envelopeReserve Q k := by
  by_contra! fail
  obtain ⟨I,ind,largest,_,s,v,_,_,_,_,_,_,_,_,_,_⟩ :=
    unpaid_requires_large_exceptional_clique Q D k six conn reg crit fail
  have exp := regular_factorCritical_exposure Q crit v D reg
  have env := (envelope_reserve_account Q D).2
  have trunc := envelopeReserve_le_truncation Q D k (fun x => (reg x).le)
  have zero : baseReserve Q D=0 := by omega
  have ord := factorCritical_order_rank Q crit v
  have par := regular_even_on_odd Q D (show Odd (Nat.card X) from ⟨matchingEdges Q,by omega⟩) reg
  have paid := exceptional_large_clique_positive Q I ind largest D (by omega) par reg crit s
  omega

/-- Every finite host with degree bound D≥3, D≠4, satisfies the actual
envelope inequality at every column k, componentwise on its own labels. -/
theorem reserve_except_degree_four (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (notFour : D≠4) (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    minimumExposure G D≤envelopeReserve G k := by
  by_contra! fail
  obtain ⟨c,unpaid,reg,crit,par,four,_⟩ := unpaid_graph_regular_obstruction G D k large cap fail
  have evenD := Nat.even_iff.mp par
  have six : 6≤D := by omega
  let _ : Nonempty c.supp := ⟨⟨c.nonempty_supp.choose,c.nonempty_supp.choose_spec⟩⟩
  have paid := regular_large_degree_envelope c.toSimpleGraph D k six c.connected_toSimpleGraph
    (fun v => (component_degree_eq G c v).trans (reg v)) crit
  omega

/-- The strengthened rank deficit on a strict source row, without a reserve
premise in all presently settled degrees. -/
theorem strict_row_paid_except_four {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (large : 3≤D) (notFour : D≠4) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤k+1) (strict : G.edgeSet.ncard<rowEnergy n m r) :
    matchingEdges G+minimumExposure G D+1≤rowCount s t r :=
  strict_row_of_envelope_payment hs ht n m hn hm pn pm G r D k row height
    (reserve_except_degree_four G D k large notFour cap) strict

#print axioms exceptional_large_clique_positive
#print axioms regular_large_degree_envelope
#print axioms reserve_except_degree_four
#print axioms strict_row_paid_except_four
end JSP452Audit.StarHost
