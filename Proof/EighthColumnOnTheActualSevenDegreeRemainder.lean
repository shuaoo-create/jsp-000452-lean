import SmallPortPairsCannotReachTheSevenMenu
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_eighth_column_options (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    let L := widthAt F.n F.m F.r 8
    let c := H.midCut.ncard
    let rho := minimumExposure (R.erased.induce H.midCutᶜ) 7
    L-c≤R.slotDamage 2+rho ∨ L+1+F.r≤R.slotDamage 2+R.slotDamage 5 := by
  intro L c rho
  by_cases live : 0<L
  · obtain ⟨a,b,pa,pb,hgt,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      (by decide : 0<8) live
    obtain ⟨nlim,mlim⟩ := strict_nine_two_long_heads_at_most_seven F paid nine R long
    have na := (original_threshold_prefix F.n F.hn a ⟨0,F.hs⟩).mpr red
    have mb := (original_threshold_prefix F.m F.hm b ⟨0,F.ht⟩).mpr blue
    have ma := nlim ⟨0,F.hs⟩
    have nb := mlim ⟨0,F.ht⟩
    have a2 : 2≤a := by omega
    have b2 : 2≤b := by omega
    have small (x) : R.starTax x≤R.slotDamage x := Nat.min_le_right _ _
    have red2 := (small a).trans (R.port_slot_decreases a2)
    have blue2 := (small b).trans (R.port_slot_decreases b2)
    have cap := (H.degree_caps (nine_erased_degree_cap F paid nine R)).2.1
    have retain {x y k : ℕ} (px : 0<x) (py : 0<y) (height : x+y-1=8) (tax : k≤R.slotDamage 2)
        (width : ExactTypedWidth R.erased x y (L-k)) : L-c≤R.slotDamage 2+rho := by
      have shrunk := typed_width_after_deletion R.erased H.midCut px py width
      have fee := typed_width_exposure_at_cap _ 7 x y _ (by decide) cap px py height shrunk
      change L-k-c≤rho at fee;omega
    change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at w
    by_cases hitA : R.starTax a<originalThresholdCount F.n a
    · left;apply retain pa pb hgt red2;rw [w]
      exact R.active_port_rectangle F.n F.m F.hn F.hm hitA blue F.row
    by_cases hitB : R.starTax b<originalThresholdCount F.m b
    · left;apply retain pb pa (by omega : b+a-1=8) blue2;rw [w,Nat.add_comm (originalThresholdCount F.n a)]
      exact R.active_port_rectangle F.m F.n F.hm F.hn hitB red (swap_positive_forcing_row _ _ _ F.row)
    · right
      by_cases big : 5≤a
      · have smallA := (small a).trans (R.port_slot_decreases big);omega
      · have smallB := (small b).trans (R.port_slot_decreases (by omega : 5≤b));omega
  · left;omega

theorem strict_nine_final_exterior_exposure_at_least_ten (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    10≤minimumExposure (R.erased.induce H.midCutᶜ) 7 := by
  let P := R.totalCapacity
  let e := R.portCount
  let M := R.slotDamage
  let L := widthAt F.n F.m F.r
  let b := H.upper.ncard
  let c := H.midCut.ncard
  let rho := minimumExposure (R.erased.induce H.midCutᶜ) 7
  have large := (strict_nine_two_long_capacity_is_large F paid nine R long H).2.2
  change 14≤P at large
  have ec := R.physical_tip_and_root_counts.2.2
  change R.looseRoots.ncard+e≤2 at ec
  have slots := R.port_slot_sizes
  change 3*M 2≤2*P+4+e ∧ 4*M 3≤2*P+4+2*e ∧ _ at slots
  have five : 6*M 5≤2*P+4+4*e := by change 6*(e+(2*P+4-2*e)/6)≤_;omega
  obtain ⟨_,_,V,_,_,_,pay⟩ := strict_nine_final_seven_menu F paid nine R long H
  change 2*P+9+e+b+c≤L 8+L 9+highestWidth F.n F.m F.r at pay
  have ninth := (strict_nine_seven_head_ninth_shadow F paid nine R long H).1
  change L 9-b≤M 3+7 at ninth
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have options := strict_nine_eighth_column_options F paid nine R long H
  change L 8-c≤M 2+rho ∨ L 8+1+F.r≤M 2+M 5 at options
  change 10≤rho
  rcases options with hit|zero <;> omega

#print axioms strict_nine_eighth_column_options
#print axioms strict_nine_final_exterior_exposure_at_least_ten
end JSP452Audit.StarHost
