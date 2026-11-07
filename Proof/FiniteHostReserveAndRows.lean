import FourRegularComponentEnvelope
import StrictSourceClassificationBridge
import FinalDescentLengths
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

/-- All finite hosts of maximum degree at most D, all truncation heights. -/
theorem finite_host_envelope_reserve (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) : minimumExposure G D≤envelopeReserve G k := by
  by_cases four : D=4
  · subst D
    by_contra! fail
    obtain ⟨c,unpaid,reg,crit,_⟩ := unpaid_graph_regular_obstruction G 4 k large cap fail
    let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
    exact (Nat.not_lt_of_ge (four_regular_component_envelope c.toSimpleGraph k c.connected_toSimpleGraph
      (fun v => (component_degree_eq G c v).trans (reg v)) crit)) unpaid
  exact reserve_except_degree_four G D k large four cap

theorem original_row_envelope_price {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (large : 3≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (height : diagonal n m (r+2)≤k+1) :
    rowEnergy n m r+matchingEdges G+minimumExposure G D≤G.edgeSet.ncard+rowCount s t r :=
  row_price_of_envelope_payment hs ht n m hn hm pn pm G r D k row height (finite_host_envelope_reserve G D k large cap)

/-- At a minimum-rank strict source, d=N−ν is at least ρ+1 and at least two. -/
theorem minimal_strict_source_deficit (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    matchingEdges F.G+minimumExposure F.G D+1≤F.rank ∧
      minimumExposure F.G D+1≤F.rank-matchingEdges F.G ∧ 2≤F.rank-matchingEdges F.G := by
  intro D
  have large : 3≤D := strict_source_degree_at_least_three F paid
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have height : diagonal F.n F.m (F.r+2)≤D+1 := by dsimp [D] at *;omega
  have charge := strict_row_of_envelope_payment F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r D D
    F.row height (finite_host_envelope_reserve F.G D D large cap) F.strict
  change matchingEdges F.G+minimumExposure F.G D+1≤F.rank at charge
  obtain ⟨width,exposure⟩ := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  change highestWidth F.n F.m F.r≤minimumExposure F.G D at exposure
  exact ⟨charge,by omega,by omega⟩

#print axioms finite_host_envelope_reserve
#print axioms original_row_envelope_price
#print axioms minimal_strict_source_deficit
end JSP452Audit.StarHost
