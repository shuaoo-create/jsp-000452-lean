import AllUnitAxesCannotPayOnTheSameActualPortHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_no_nine_leaf (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r)) (narrow:highestWidth F.n F.m F.r≤2)
    (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t) :
    (∀i,F.n i≤8) ∧ (∀j,F.m j≤8) := by
  let O := W.outside
  have orig (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have cap (v:↥(W.supportᶜ:Set F.X)) := (induced_neighbor_count_le F.G W.supportᶜ v).trans (orig v.val)
  obtain ⟨B,first⟩ := complete_degree_stage_exists O 10
  obtain ⟨C,second⟩ := complete_degree_stage_exists (O.induce Bᶜ) 9
  have low (x) : Nat.card ((O.induce Bᶜ).neighborSet x)≤9 := Nat.le_of_lt_succ (complete_stage_lowers_cap O 10 B cap first x)
  have endcap (x) : Nat.card (((O.induce Bᶜ).induce Cᶜ).neighborSet x)≤8 :=
    Nat.le_of_lt_succ (complete_stage_lowers_cap _ 9 C low second x)
  have bound := nested_deletion_cap O B C 8 endcap
  have short := ten_port_steps_outlast_nine F paid ten W narrow length B first C second
  have fit : W.steps F.r≤W.half := (Nat.sub_le _ _).trans (W.size_and_fee (strict_ten_inventory F paid ten).1).2.2.2.2.1
  have no : ¬(0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9) := by
    intro heads
    have endpt := ten_port_exterior_stock F W deep length
    have count := endpt.2 (nestedRemoved B C) 9 (by decide) (fun v => by
      change Nat.card ((O.induce (nestedRemoved B C)ᶜ).neighborSet v)<9;have := bound v;omega) heads
    rw [nested_removed_card] at count
    apply ten_all_axes_contradict_port_support F paid ten W narrow deep length
    intro j lo hi
    have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht lo hi
    have len := endpt.1
    have debt := (ten_port_exterior_matching_endpoints F W deep length).1
    have live : 0<widthAt F.n F.m F.r j := by omega
    obtain ⟨x,y,xp,yp,height,red,blue,width⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm lo live
    have win : WinsHeight F.n F.m F.r j x y := ⟨xp,yp,height,red,blue,width⟩
    refine ⟨x,y,win,?_⟩
    by_contra! nonunit
    have price := ten_nine_head_mixed_support_stock F paid ten W narrow deep length heads j x y (by omega) hi
      (by omega) (by omega) win
    omega
  constructor
  · intro i;by_contra! big;exact no (Or.inl (Nat.zero_lt_of_lt ((original_threshold_prefix F.n F.hn 9 i).mp big)))
  · intro i;by_contra! big;exact no (Or.inr (Nat.zero_lt_of_lt ((original_threshold_prefix F.m F.hm 9 i).mp big)))

#print axioms ten_port_no_nine_leaf
end JSP452Audit.StarHost
