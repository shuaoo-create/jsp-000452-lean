import TheTwoLowColumnsAndTheNinthOnTheSameGraphs
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_single_short_large_mixed_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 9 x y) : False := by
  let P := R.totalCapacity
  let W := componentBudget (F.G.induce R.chosen) F.n
  let J := commonErasedDemand F.n W R.roots.ncard P
  let L := widthAt F.n F.m F.r
  let A := R.axisAllowance F.n F.m F.r
  let X := ∑i,(F.n i-1)/2
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let b := F.m ⟨0,F.ht⟩
  have zero := strict_nine_large_top_forces_joined_units F paid nine R aligned long short winner
  change originalThresholdCount J 2=0 at zero
  have fit : W.loss≤P := (nine_long_side_actual_source_prices F paid nine R long).2.2.1
  have bound := (common_threshold_floors F.n F.hn F.pn W R.roots.ncard P 2 fit).2.1
  change originalThresholdCount F.n 2≤P+originalThresholdCount J 2 at bound
  have few : originalThresholdCount F.n 2≤R.totalCapacity := by change _≤P;omega
  have lower := strict_nine_two_low_and_ninth_price F paid nine R long short few winner
  have area := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
  have positive := (strict_nine_root_deleted_row F paid nine R).1
  have space : F.t+2*(∑i,(F.m i-1)/2)≤P := by change F.t+2*(∑i,(F.m i-1)/2)+_≤P+1 at area;omega
  have axes := R.all_axis_allowances F.n F.m F.ht F.hn F.hm F.pn F.pm F.row space
  have total := fold_low_top_boundary 9 b d 1 X L R.jointPrice A (by decide) lower
    (fun j lo _ => strict_nine_higher_boundary_cost F paid nine R long short j lo few) axes
  apply strict_nine_joint_allowance_six_impossible F paid nine R aligned
  change 2*(∑i∈Finset.range 8,L (i+2))+2*d≤(∑i∈Finset.range 8,R.jointPrice (i+2))+6
  change 2*(∑i∈Finset.range 8,L (i+2))+2*d≤(∑i∈Finset.range 8,R.jointPrice (i+2))+4 at total
  omega

theorem strict_nine_single_short_only_two_eight (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) :
    F.m ⟨0,F.ht⟩=8 ∧ WinsHeight F.n F.m F.r 9 2 8 ∧
    (∀x y,WinsHeight F.n F.m F.r 9 x y → x=2 ∧ y=8) ∧ originalThresholdCount F.m 8≤F.r := by
  have top : diagonal F.n F.m (F.r+2)=10 := by omega
  have live := actual_height_positive F.n F.m F.live top 9 (by decide)
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have nr := red ⟨0,F.hs⟩
  have mr := blue ⟨0,F.ht⟩
  rw [nine] at nr mr
  have only (x y) (win : WinsHeight F.n F.m F.r 9 x y) : x=2 ∧ y=8 := by
    obtain ⟨px,py,hgt,yes,hit,winnerWidth⟩ := win
    have ncap := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).mpr yes
    have mcap := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).mpr hit
    have y2 : 2≤y := by omega
    by_contra! bad
    have x3 : 3≤x := by omega
    exact strict_nine_single_short_large_mixed_impossible F paid nine R aligned long short ⟨x,y,x3,y2,px,py,hgt,yes,hit,winnerWidth⟩
  obtain ⟨x,y,px,py,hgt,yes,hit,area⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by decide : 0<9) live
  have actual : WinsHeight F.n F.m F.r 9 x y := ⟨px,py,hgt,yes,hit,area⟩
  obtain ⟨rfl,rfl⟩ := only x y actual
  have blueMax := (original_threshold_prefix F.m F.hm 8 ⟨0,F.ht⟩).mpr hit
  obtain ⟨_,_,_,_,i,j,_,_,_,shape,_⟩ := strict_nine_original_peak F paid nine
  have nh := (original_threshold_prefix F.n F.hn 3 i).mp (by omega)
  have sparse := strict_nine_eight_three_rectangle_absent F paid nine 3 8 (Or.inr ⟨rfl,rfl⟩) (Nat.zero_lt_of_lt nh) hit
  exact ⟨by omega,actual,only,by omega⟩

#print axioms strict_nine_single_short_large_mixed_impossible
#print axioms strict_nine_single_short_only_two_eight
end JSP452Audit.StarHost
