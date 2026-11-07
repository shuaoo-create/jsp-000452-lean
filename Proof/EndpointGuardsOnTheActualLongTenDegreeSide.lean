import ActualMissingThresholdOnTheLongTenDegreeSide
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_long_side_exterior_endpoints (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s) :
    let P := R.capacity
    let a := R.roots.ncard
    let W := componentBudget (F.G.induce R.core) F.n
    let delta := P-W.loss
    let d' := F.rank-matchingEdges F.G
    a+F.r+2*(d'+∑j,(F.m j-1)/2)+delta≤F.s-P ∧
      a+F.r+2*(d'+delta+∑i,(W.entries F.n i-1)/2)≤F.t := by
  intro P a W delta d'
  have paidRow := ten_long_side_two_prices F paid ten R small many long
  obtain ⟨alive,_,fit,rank,_,_,_,_⟩ := paidRow
  change 0<W.len at alive
  change W.loss≤P at fit
  change rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta at rank
  let O := F.G.induce R.rest
  obtain ⟨S,tight,critical⟩ := exists_critical_barrier O
  have pos : 2≤d' := (ten_physical_root_deleted_row F paid R).1
  have row := (ten_same_budget_on_two_graphs F paid R).1.1
  change ForcingRow O W.len F.t (padDemand (W.entries F.n)) (padDemand F.m) (F.r+a) at row
  have prices := full_row_endpoint_guards O alive F.ht (W.entries F.n) F.m
    (W.entries_positive F.n F.pn) F.pm row S tight (fun c => (critical c).2) (d'+delta) (by omega) (by
      change R.outsideRank+(d'+delta)=rowCount W.len F.t (F.r+a);omega)
  change S.ncard+(F.r+a)+2*(d'+delta+∑i,(W.entries F.n i-1)/2)≤F.t ∧
    S.ncard+(F.r+a)+2*(d'+delta+∑j,(F.m j-1)/2)≤W.len at prices
  have len : W.len=F.s-W.loss := rfl
  dsimp only [delta] at prices ⊢
  omega

#print axioms ten_long_side_exterior_endpoints
end JSP452Audit.StarHost
