import TheTenthColumnPaysOrControlsTheBlueClassDifference
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_two_low_and_tenth_price (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (many:1≤R.eta) (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (aligned:highestWidth F.n F.m F.r≤R.eta) (long : R.capacity<F.s) (short : F.t≤R.capacity)
    (few : originalThresholdCount F.n 2≤R.capacity)
    (mixed : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 10 x y) :
    let d := F.rank-matchingEdges F.G
    let X := ∑i,(F.n i-1)/2
    let L := widthAt F.n F.m F.r
    let A := R.axisAllowance F.n F.m F.r
    2*L 2+2*L 3+2*L 10+2*X+2*d≤R.jointPrice 2+R.jointPrice 3+R.jointPrice 10+A 2+A 3+2*R.eta+4 := by
  intro d X L A
  let P := R.capacity
  let a := R.roots.ncard
  let Y := ∑i,(F.m i-1)/2
  let W := componentBudget (F.G.induce R.core) F.n
  let delta := P-W.loss
  let u := F.s-originalThresholdCount F.n 2
  let q := P-(F.t+2*Y)+1
  let g := originalThresholdCount F.m
  have endpt := (ten_common_endpoint_guards F paid R).1
  change a+F.r+2*(d+X)≤F.t at endpt
  have space := ((ten_short_core_endpoint F paid R).2 short).2.2
  change F.t+2*Y+d≤P+1 at space
  have mass := (ten_short_core_mass F paid R).2 short
  change (∑j,F.m j)+d≤P+a+R.eta at mass
  have reserve : 2≤d := (ten_physical_root_deleted_row F paid R).1
  have out := (ten_long_side_exterior_endpoints F paid ten R small many long).1
  change a+F.r+2*(d+Y)+delta≤F.s-P at out
  have size : a+F.r+2*(d+Y)+delta≤u := by change originalThresholdCount F.n 2≤P at few;dsimp only [u];omega
  have volume := ten_doubled_unit_volume F paid ten R small many long few
  change P+F.r+2*d+2*Y≤2*u+2*delta+R.eta at volume
  have topFee := ten_single_short_large_top_price F paid ten R balanced short mixed
  have cases := ten_large_top_extra_or_blue_difference F paid ten R short mixed
  change 2*L 10+2*X+2*d+2*q≤R.jointPrice 10 ∨ L 10+g 3≤highestWidth F.n F.m F.r+g 2 at cases
  have useTop : 2*L 10+2*X+2*d+2*q≤R.jointPrice 10 ∨ 2*L 10+2*g 3≤2*highestWidth F.n F.m F.r+2*g 2 := by omega
  have budget : a+2*P≤R.jointPrice 10 := by dsimp only [TenBlockPartition.jointPrice,a,P];omega
  have pay : 2*L 10+2*X+2*d≤R.jointPrice 10 := topFee.trans budget
  have sort : g 3≤g 2 := threshold_anti_height F.m (by decide : 2≤3)
  have count : g 2≤F.t := original_threshold_le_length F.m 2
  obtain ⟨i,j,_,_,_,_,shape,_⟩ := strict_ten_true_factor_peak F paid ten
  have blue3 : 0<g 3 := Nat.zero_lt_of_lt ((original_threshold_prefix F.m F.hm 3 j).mp (by omega))
  have blue2 : 0<g 2 := blue3.trans_le sort
  have unitCount := units_and_twos_below_mass F.m F.pm
  change F.t+g 2≤∑j,F.m j at unitCount
  apply low_pair_and_top_with_core_defect F.t F.r a P u delta d R.eta (highestWidth F.n F.m F.r) X Y q (g 2) (g 3) (L 2) (L 3) (L 10)
    (R.jointPrice 2) (R.jointPrice 3) (R.jointPrice 10) (A 2) (A 3)
    aligned balanced endpt (by omega) rfl count sort (by omega) size volume pay budget useTop
  · by_cases hit : ∃y,WinsHeight F.n F.m F.r 2 2 y
    · obtain ⟨y,who⟩ := hit
      obtain rfl : y=1 := by have := who.2.2.1;have := who.2.1;omega
      have present := actual_height_positive F.n F.m F.live (by omega : diagonal F.n F.m (F.r+2)=10+1) 2 (by decide)
      have price := ten_two_head_inventory_cost F paid ten R small many long 2 1 (by decide) blue2 who present
      rw [original_threshold_one F.m F.pm] at price
      exact Or.inr ⟨price,ten_matching_axis_qbound F paid ten R short 2 (by decide) who⟩
    · exact Or.inl (ten_no_two_head_column_paid F paid ten R small many balanced long short 2 (by decide) hit)
  · by_cases hit : ∃y,WinsHeight F.n F.m F.r 3 2 y
    · obtain ⟨y,who⟩ := hit
      obtain rfl : y=2 := by have := who.2.2.1;have := who.2.1;omega
      have present := actual_height_positive F.n F.m F.live (by omega : diagonal F.n F.m (F.r+2)=10+1) 3 (by decide)
      exact Or.inr (ten_two_head_inventory_cost F paid ten R small many long 3 2 (by decide) blue3 who present)
    · exact Or.inl (ten_no_two_head_column_paid F paid ten R small many balanced long short 3 (by decide) hit)

#print axioms ten_two_low_and_tenth_price
end JSP452Audit.StarHost
