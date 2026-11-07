import TheSecondThirdAndTenthColumnsOnTheSamePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_single_short_large_mixed_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 10 x y) : False := by
  let P := R.capacity
  let W := componentBudget (F.G.induce R.core) F.n
  let J := commonErasedDemand F.n W R.roots.ncard P
  let L := widthAt F.n F.m F.r
  let A := R.axisAllowance F.n F.m F.r
  let X := ∑i,(F.n i-1)/2
  let d := F.rank-matchingEdges F.G
  let b := F.m ⟨0,F.ht⟩
  have zero := ten_large_top_forces_joined_units F paid ten R small excess balanced long short winner
  change originalThresholdCount J 2=0 at zero
  have fit : W.loss≤P := (ten_long_side_two_prices F paid ten R small (by omega) long).2.2.1
  have bound := (common_threshold_floors F.n F.hn F.pn W R.roots.ncard P 2 fit).2.1
  change originalThresholdCount F.n 2≤P+originalThresholdCount J 2 at bound
  have few : originalThresholdCount F.n 2≤R.capacity := by change _≤P;omega
  have lower := ten_two_low_and_tenth_price F paid ten R small (by omega) balanced (by omega) long short few winner
  have area := ((ten_short_core_endpoint F paid R).2 short).2.2
  have positive := (ten_physical_root_deleted_row F paid R).1
  have space : F.t+2*(∑i,(F.m i-1)/2)≤P := by change F.t+2*(∑i,(F.m i-1)/2)+_≤P+1 at area;omega
  have axes := R.all_axis_allowances F.n F.m F.ht F.hn F.hm F.pn F.pm F.row space
  let rho := R.eta+2
  have total := fold_low_top_boundary 10 b d rho X L R.jointPrice A (by decide) (by
    change 2*L 2+2*L 3+2*L 10+2*X+2*d≤R.jointPrice 2+R.jointPrice 3+R.jointPrice 10+A 2+A 3+2*rho
    dsimp only [rho];omega)
    (fun j lo _ => by
      have hh := ten_higher_boundary_cost F paid ten R small (by omega) balanced long short j lo few
      change 2*L j≤R.jointPrice j+A j+(if j=b+1 then 2*highestWidth F.n F.m F.r else 0) at hh
      split_ifs at hh ⊢ <;> omega) axes
  apply ten_joint_payment_impossible F paid ten R (4*rho) (by dsimp only [rho];omega)
  change 2*(∑i∈Finset.range 9,L (i+2))+2*d≤(∑i∈Finset.range 9,R.jointPrice (i+2))+4*rho
  exact total

theorem ten_single_short_only_two_nine (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity) :
    F.m ⟨0,F.ht⟩=9 ∧ WinsHeight F.n F.m F.r 10 2 9 ∧
    (∀x y,WinsHeight F.n F.m F.r 10 x y → x=2 ∧ y=9) ∧ originalThresholdCount F.m 9≤F.r+highestWidth F.n F.m F.r := by
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  have live := actual_height_positive F.n F.m F.live top 10 (by decide)
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have nr := red ⟨0,F.hs⟩
  have mr := blue ⟨0,F.ht⟩
  rw [ten] at nr mr
  have only (x y) (win : WinsHeight F.n F.m F.r 10 x y) : x=2 ∧ y=9 := by
    obtain ⟨px,py,hgt,yes,hit,winnerWidth⟩ := win
    have ncap := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).mpr yes
    have mcap := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).mpr hit
    have y2 : 2≤y := by omega
    by_contra! bad
    have x3 : 3≤x := by omega
    exact ten_single_short_large_mixed_impossible F paid ten R small excess balanced long short ⟨x,y,x3,y2,px,py,hgt,yes,hit,winnerWidth⟩
  obtain ⟨x,y,px,py,hgt,yes,hit,area⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by decide : 0<10) live
  have actual : WinsHeight F.n F.m F.r 10 x y := ⟨px,py,hgt,yes,hit,area⟩
  obtain ⟨rfl,rfl⟩ := only x y actual
  have blueMax := (original_threshold_prefix F.m F.hm 9 ⟨0,F.ht⟩).mpr hit
  have exactHead : F.m ⟨0,F.ht⟩=9 := by omega
  have sparse := large_blue_peak_prefix F.hs F.ht F.n F.m F.hn F.hm F.live (D:=10) top mr.le
  rw [exactHead] at sparse
  exact ⟨exactHead,actual,only,sparse⟩


#print axioms ten_single_short_large_mixed_impossible
#print axioms ten_single_short_only_two_nine
end JSP452Audit.StarHost
