import NeitherActualForestCanHaveANineLeafHeadOnThePortSupport
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_actual_last_two_cost (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (narrow:highestWidth F.n F.m F.r≤2)
    (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (eight:0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8)
    (H:ThreeDegreeStages W.outside 8) :
    (∀i,F.n i≤8) ∧ (∀i,F.m i≤8) ∧
    H.midCut.ncard<W.steps F.r ∧ W.steps F.r≤H.lastCut.ncard ∧
      2*W.rank+W.fee+1+H.upper.ncard+H.midCut.ncard≤widthAt F.n F.m F.r 9+widthAt F.n F.m F.r 10+highestWidth F.n F.m F.r := by
  obtain ⟨red,blue⟩ := ten_port_no_nine_leaf F paid ten W narrow deep length
  have cap (v:↥(W.supportᶜ:Set F.X)) := (induced_neighbor_count_le F.G W.supportᶜ v).trans
    (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq ten)
  have high := (H.degree_caps cap).2.2
  have stock := (ten_port_exterior_stock F W deep length).2 H.lastCut 8 (by decide) high eight
  have thick := ten_eight_leaf_support_stock F paid ten W narrow deep length red blue
  have fits : W.steps F.r≤H.lastCut.ncard := by
    have price := (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.2.2.1
    change W.rank-(F.r+1)≤H.lastCut.ncard;omega
  have short := ten_port_steps_outlast_nine F paid ten W narrow length H.upper H.first H.middle H.second
  rw [←nested_removed_card] at short
  obtain ⟨V,_,_,_,_,_,fee⟩ := ten_port_eight_exit_cost F paid ten W length H short fits
  exact ⟨red,blue,short,fits,fee⟩

#print axioms ten_port_actual_last_two_cost
end JSP452Audit.StarHost
