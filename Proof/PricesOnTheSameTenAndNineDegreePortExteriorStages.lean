import OneStrictlySmallerRowAndItsActualExteriorCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_first_two_stage_cost (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (B:Set ↥(W.supportᶜ:Set F.X)) (first:CompleteDegreeStage W.outside 10 B)
    (C:Set ↥(Bᶜ:Set _)) (second:CompleteDegreeStage (W.outside.induce Bᶜ) 9 C)
    (fit:W.steps F.r≤B.ncard+C.ncard) :
    let k := W.steps F.r
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 10
    W.rank+W.fee+1+min k B.ncard≤L+h ∧ W.fee+1+min k B.ncard≤k+h := by
  intro k h L
  obtain ⟨V,num,actual⟩ := two_stage_exact_prefix W.outside 9 B first C second k fit
  obtain ⟨_,small,row,fee⟩ := W.whole_piece_cost F paid ten length V num
  change W.outside.edgeSet.ncard+W.fee+1≤(W.outside.induce Vᶜ).edgeSet.ncard+10*V.ncard+h at fee
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (W.outside.induce Vᶜ) (F.r+(V.ncard+W.rank)) row small
  have taxes := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 9
    (show diagonal F.n F.m (F.r+2)=11 by omega) (k+W.rank)
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+(k+W.rank))+9*(k+W.rank)+L+h at taxes
  rw [num] at fee pay
  have cost : W.piece.edgeSet.ncard=10*W.rank+W.fee := (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.2.2.2.2.2.1
  have split := erase_internal_edge_count F.G W.supportᶜ
  change F.G.edgeSet.ncard=W.piece.edgeSet.ncard+W.outside.edgeSet.ncard at split
  have old := F.strict
  change W.outside.edgeSet.ncard=(W.outside.induce Vᶜ).edgeSet.ncard+9*k+min k B.ncard at actual
  omega

theorem ten_port_steps_outlast_ten (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (B:Set ↥(W.supportᶜ:Set F.X)) (first:CompleteDegreeStage W.outside 10 B) : B.ncard<W.steps F.r := by
  by_contra! fit
  obtain ⟨C,second⟩ := complete_degree_stage_exists (W.outside.induce Bᶜ) 9
  have cut := (ten_port_first_two_stage_cost F paid ten W length B first C second (by omega)).2
  rw [min_eq_left fit] at cut
  have book := W.size_and_fee (strict_ten_inventory F paid ten).1
  omega

#print axioms ten_port_first_two_stage_cost
#print axioms ten_port_steps_outlast_ten
end JSP452Audit.StarHost
