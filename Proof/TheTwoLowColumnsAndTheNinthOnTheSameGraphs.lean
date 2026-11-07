import TheSingleRemainingHigherBlueBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_two_low_and_ninth_price (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity)
    (few : originalThresholdCount F.n 2≤R.totalCapacity)
    (mixed : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 9 x y) :
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    let X := ∑i,(F.n i-1)/2
    let L := widthAt F.n F.m F.r
    let A := R.axisAllowance F.n F.m F.r
    2*L 2+2*L 3+2*L 9+2*X+2*d≤R.jointPrice 2+R.jointPrice 3+R.jointPrice 9+A 2+A 3+2 := by
  intro d X L A
  let P := R.totalCapacity
  let a := R.roots.ncard
  let Y := ∑i,(F.m i-1)/2
  let W := componentBudget (F.G.induce R.chosen) F.n
  let delta := P-W.loss
  let u := F.s-originalThresholdCount F.n 2
  let q := P-(F.t+2*Y)+1
  let g := originalThresholdCount F.m
  have endpt := (strict_nine_original_root_endpoints F paid nine R).1
  change a+F.r+2*(d+X)≤F.t at endpt
  have space := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
  change F.t+2*Y+d≤P+1 at space
  have mass := (strict_nine_short_box_masses F paid nine R).2 short
  change (∑j,F.m j)+d≤P+2 at mass
  have roof : 1≤a := R.root_count.1
  have reserve : 2≤d := (strict_nine_root_deleted_row F paid nine R).1
  have out := (nine_long_side_exterior_endpoints F paid nine R long).1
  change a+F.r+2*(d+Y)+delta≤F.s-P at out
  have size : a+F.r+2*(d+Y)+delta≤u := by change originalThresholdCount F.n 2≤P at few;dsimp only [u];omega
  have volume := strict_nine_doubled_unit_volume F paid nine R long few
  change P+F.r+2*d+2*Y≤2*u+2*delta+1 at volume
  have topFee := strict_nine_single_short_large_top_price F paid nine R short mixed
  have cases := strict_nine_large_top_extra_or_blue_difference F paid nine R short mixed
  change 2*L 9+2*X+2*d+2*q≤R.jointPrice 9 ∨ L 9+g 3≤g 2 at cases
  have useTop : 2*L 9+2*X+2*d+2*q≤R.jointPrice 9 ∨ 2*L 9+2*g 3≤2*1+2*g 2 := by omega
  have budget : a+2*P≤R.jointPrice 9 := by dsimp only [NinePortRegion.jointPrice,a,P];omega
  have pay : 2*L 9+2*X+2*d≤R.jointPrice 9 := topFee.trans budget
  have sort : g 3≤g 2 := threshold_anti_height F.m (by decide : 2≤3)
  have count : g 2≤F.t := original_threshold_le_length F.m 2
  obtain ⟨_,_,_,_,i,j,_,_,_,shape,_⟩ := strict_nine_original_peak F paid nine
  have blue3 : 0<g 3 := Nat.zero_lt_of_lt ((original_threshold_prefix F.m F.hm 3 j).mp (by omega))
  have blue2 : 0<g 2 := blue3.trans_le sort
  have unitCount := units_and_twos_below_mass F.m F.pm
  change F.t+g 2≤∑j,F.m j at unitCount
  apply low_pair_and_top_price F.t F.r a P u delta d 1 1 X Y q (g 2) (g 3) (L 2) (L 3) (L 9)
    (R.jointPrice 2) (R.jointPrice 3) (R.jointPrice 9) (A 2) (A 3)
    le_rfl reserve endpt (by omega) rfl count sort (by omega) size volume pay budget useTop
  · by_cases hit : ∃y,WinsHeight F.n F.m F.r 2 2 y
    · obtain ⟨y,who⟩ := hit
      obtain rfl : y=1 := by have := who.2.2.1;have := who.2.1;omega
      have present := actual_height_positive F.n F.m F.live (by omega : diagonal F.n F.m (F.r+2)=9+1) 2 (by decide)
      have price := nine_two_head_inventory_cost F paid nine R long 2 1 (by decide) blue2 who present
      rw [original_threshold_one F.m F.pm] at price
      exact Or.inr ⟨price,strict_nine_matching_axis_qbound F paid nine R short 2 (by decide) who⟩
    · exact Or.inl (strict_nine_no_two_head_column_paid F paid nine R long short 2 (by decide) hit)
  · by_cases hit : ∃y,WinsHeight F.n F.m F.r 3 2 y
    · obtain ⟨y,who⟩ := hit
      obtain rfl : y=2 := by have := who.2.2.1;have := who.2.1;omega
      have present := actual_height_positive F.n F.m F.live (by omega : diagonal F.n F.m (F.r+2)=9+1) 3 (by decide)
      exact Or.inr (nine_two_head_inventory_cost F paid nine R long 3 2 (by decide) blue3 who present)
    · exact Or.inl (strict_nine_no_two_head_column_paid F paid nine R long short 3 (by decide) hit)

#print axioms strict_nine_two_low_and_ninth_price
end JSP452Audit.StarHost
