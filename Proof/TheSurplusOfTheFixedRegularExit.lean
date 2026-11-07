import TheChosenRegularSuccessorStopsAtSevenOrSix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem zero_exposure_above_every_degree {X:Type u} [Finite X] (G:SimpleGraph X) (a:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)<a) : minimumExposure G a=0 := by
  obtain ⟨M,_,_,opt⟩ := minimumExposure_attained G a
  have empty : exposedFull G M a=∅ := Set.eq_empty_of_forall_notMem (fun x mem => (cap x).ne mem.2)
  rw [empty,Set.ncard_empty] at opt;exact opt.symm

theorem actual_row_height_from_cap {X:Type u} [Finite X] (G:SimpleGraph X) {s t r:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀i,1≤m i) (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (live:0<rowCount s t r) (a:ℕ) (cap:∀v,Nat.card (G.neighborSet v)≤a) :
    diagonal n m (r+2)≤a+1 := by
  have larger (v):Nat.card (G.neighborSet v)≤a+1 := (cap v).trans (by omega)
  have price := (widthAt_le_uniformEnvelope hs ht n m hn hm pn pm G r (a+2) row (by omega)).trans
    ((uniformEnvelope_le_deletion G (a+1) (by omega)).trans (deletionBudget_le_minimumExposure G (a+1) (by omega) larger))
  rw [zero_exposure_above_every_degree G _ (fun v => Nat.lt_succ_of_le (cap v))] at price
  have low := height_below_empty_column n m live (Nat.eq_zero_of_le_zero price)
  omega

namespace TenRegularExit
variable {F:StrictFamily.{u}} {A:PricedTenMenu F} {a inc:ℕ} (E:TenRegularExit A a inc)
abbrev graph := (F.G.induce A.K.supportᶜ).induce E.vertexSetᶜ
noncomputable def surplus := E.graph.edgeSet.ncard-rowEnergy F.n F.m (F.r+A.steps+A.K.P)

theorem exact_row_price (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (cases:TenRegularCases F A) (small:a≤10) :
    let r' := F.r+A.steps+A.K.P
    0<rowCount F.s F.t r' ∧ rowCount F.s F.t r'<F.rank ∧
      ForcingRow E.graph F.s F.t (padDemand F.n) (padDemand F.m) r' ∧
      diagonal F.n F.m (r'+2)≤a+1 ∧ E.graph.edgeSet.ncard=rowEnergy F.n F.m r'+E.surplus ∧
      E.surplus+(10-a)*A.K.P+5*A.K.eps+1+inc≤∑j∈Finset.range (11-a),widthAt F.n F.m F.r (a+j+1) := by
  intro r'
  have ep := A.K.positive
  have cost : 6*highestWidth F.n F.m F.r≤13*A.K.eps+6 := by unfold TenRegularCases at cases;omega
  have rank := (A.step_bounds paid ten cost).2.2
  have row := A.physical_successor_row E.vertexSet E.length
  change ForcingRow E.graph F.s F.t (padDemand F.n) (padDemand F.m) r' at row
  have tall := actual_row_height_from_cap E.graph F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row rank.1 a E.cap
  have bound := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph r' row rank.2
  have eq : E.graph.edgeSet.ncard=rowEnergy F.n F.m r'+E.surplus := by change _=_+(_-rowEnergy F.n F.m r');omega
  have cap := prefix_price_through_all_higher_columns (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm a (11-a) (A.steps+A.K.P) (by omega)
  rw [←Nat.add_assoc] at cap
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m r'+a*(A.steps+A.K.P)+_ at cap
  rw [Nat.mul_add] at cap
  have headroom : (10-a)*A.K.P+a*A.K.P=10*A.K.P := by rw [←Nat.add_mul,Nat.sub_add_cancel small]
  have price := E.price
  change (F.G.induce A.K.supportᶜ).edgeSet.ncard=E.graph.edgeSet.ncard+a*A.steps+inc at price
  have split := intact_components_plus_exterior F.G A.K.support A.K.support_closed
  rw [A.K.fee] at split
  have old := F.strict
  exact ⟨rank.1,rank.2,row,tall,eq,by omega⟩
end TenRegularExit
#print axioms zero_exposure_above_every_degree
#print axioms actual_row_height_from_cap
#print axioms TenRegularExit.exact_row_price
end JSP452Audit.StarHost
