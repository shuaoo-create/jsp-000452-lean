import PricesOnTheSameTenAndNineDegreePortExteriorStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_port_eight_exit_cost (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (H:ThreeDegreeStages W.outside 8) (mid:H.midCut.ncard<W.steps F.r) (fit:W.steps F.r≤H.lastCut.ncard) :
    let O := W.outside
    let k := W.steps F.r
    let shift := F.r+(k+W.rank)
    ∃V:Set ↥(W.supportᶜ:Set F.X),V.ncard=k ∧
      ForcingRow (O.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) shift ∧
      0<rowCount F.s F.t shift ∧ rowCount F.s F.t shift<F.rank ∧
      F.G.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+8*k+H.upper.ncard+H.midCut.ncard+10*W.rank+W.fee ∧
      2*W.rank+W.fee+1+H.upper.ncard+H.midCut.ncard≤widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r := by
  intro O k shift
  obtain ⟨V,num,fee⟩ := H.exact_last_prefix k mid fit
  obtain ⟨positive,smaller,row,_⟩ := W.whole_piece_cost F paid ten length V num
  rw [num] at positive smaller row
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (O.induce Vᶜ) shift row smaller
  have account := (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.2.2.2.2.2.1
  have split := erase_internal_edge_count F.G W.supportᶜ
  change F.G.edgeSet.ncard=W.piece.edgeSet.ncard+O.edgeSet.ncard at split
  change O.edgeSet.ncard=(O.induce Vᶜ).edgeSet.ncard+8*k+H.upper.ncard+H.midCut.ncard at fee
  have tax := ten_prefix_three_columns F.hs F.ht F.n F.m F.hn F.hm (r:=F.r) (by omega) (k+W.rank)
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m shift+8*(k+W.rank)+widthAt F.n F.m F.r 9+
    widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r at tax
  have strict := F.strict
  exact ⟨V,num,row,positive,smaller,by omega,by omega⟩

#print axioms ten_port_eight_exit_cost
end JSP452Audit.StarHost
