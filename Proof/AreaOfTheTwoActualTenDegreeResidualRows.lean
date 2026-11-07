import TwoActualColumnPricesOnTheTenDegreePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_joint_residual_area (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (many:1≤R.eta) (long:R.capacity<F.s) :
    let P := R.capacity
    let a := R.roots.ncard
    let W := componentBudget (F.G.induce R.core) F.n
    let J := commonErasedDemand F.n W a P
    (∑j∈Finset.range 9,R.basicPrice F.n F.m F.r (j+2))+10*R.eta+(F.G.induce R.roots).edgeSet.ncard+
      crossCount F.G R.roots R.rest+2*(P-W.loss)<2*interiorArea F.n F.m F.r 10+2*highestWidth F.n F.m F.r+R.epsilon := by
  intro P a W J
  obtain ⟨alive,_,fit,rankB,rankZ,_,_,_,_,fee⟩ := ten_long_side_two_prices F paid ten R small many long
  change 0<W.len at alive
  change W.loss≤P at fit
  have cb := interior_area_lower (r:=F.r+a) (D:=10) alive F.ht (W.entries F.n) F.m
    (W.entries_positive F.n F.pn) F.pm (by decide : 0<10)
  have cz := interior_area_lower (r:=F.r) (D:=10) alive F.ht J F.m
    (common_erased_positive F.n W a P) F.pm (by decide : 0<10)
  have num : W.len+W.loss=F.s := by change F.s-W.loss+W.loss=F.s;omega
  change rowCount W.len F.t (F.r+a)=R.outsideRank+(F.rank-matchingEdges F.G)+(P-W.loss) at rankB
  change rowCount W.len F.t F.r=a+R.outsideRank+(F.rank-matchingEdges F.G)+(P-W.loss) at rankZ
  have rank : rowCount W.len F.t (F.r+a)+rowCount W.len F.t F.r+2*W.loss+a=2*F.rank := by
    have positive := (ten_physical_root_deleted_row F paid R).1
    change 2≤F.rank-matchingEdges F.G at positive
    dsimp only [StrictFamily.rank,rowCount] at rankB rankZ positive ⊢;omega
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=10) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 10+highestWidth F.n F.m F.r at area
  change rowEnergy (W.entries F.n) F.m (F.r+a)+rowEnergy J F.m F.r+10*(a+2*P)+
    10*R.eta+(F.G.induce R.roots).edgeSet.ncard+crossCount F.G R.roots R.rest≤2*F.G.edgeSet.ncard+R.epsilon at fee
  have strict := F.strict
  rw [R.basic_price_sum]
  change 9*(a+2*P)+interiorArea (W.entries F.n) F.m (F.r+a) 10+interiorArea J F.m F.r 10+_+_+_+_<_
  omega

#print axioms ten_joint_residual_area
end JSP452Audit.StarHost
