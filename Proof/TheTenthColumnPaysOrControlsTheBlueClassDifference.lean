import TwoLowRowsAndTopAllowTheActualDefect
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_large_top_extra_or_blue_difference (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (short : F.t≤R.capacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 10 x y) :
    let X := ∑i,(F.n i-1)/2
    let Y := ∑j,(F.m j-1)/2
    let d := F.rank-matchingEdges F.G
    let q := R.capacity-(F.t+2*Y)+1
    2*widthAt F.n F.m F.r 10+2*X+2*d+2*q≤R.jointPrice 10 ∨
      widthAt F.n F.m F.r 10+originalThresholdCount F.m 3≤highestWidth F.n F.m F.r+originalThresholdCount F.m 2 := by
  intro X Y d q
  obtain ⟨x,y,xhi,yhi,win⟩ := winner
  have hgt := win.2.2.1
  have count := win.2.2.2.1
  have width := win.2.2.2.2.2
  by_cases two : y=2
  · right
    have nine : x=9 := by omega
    subst y;subst x
    obtain ⟨i,j,_,_,_,_,shape,_⟩ := strict_ten_true_factor_peak F paid ten
    have head := (original_threshold_prefix F.m F.hm 3 j).mp (by omega)
    have b := actual_rectangle_le_column (r:=F.r) F.n F.m F.hn F.hm (a:=9) (b:=3) (h:=11)
      (by decide) count (Nat.zero_lt_of_lt head)
    have highest := width_at_actual_top (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm
    rw [show diagonal F.n F.m (F.r+2)=11 by omega] at highest
    rw [highest] at b
    have sorted := threshold_anti_height F.m (show 2≤3 by decide)
    omega
  · left
    have rn := half_extra_pays_large_threshold F.n xhi
    have bm := half_extra_pays_large_threshold F.m (show 3≤y by omega)
    have endpoint := (ten_common_endpoint_guards F paid R).1
    have space := ((ten_short_core_endpoint F paid R).2 short).2.2
    have pos : 2≤d := (ten_physical_root_deleted_row F paid R).1
    change R.roots.ncard+F.r+2*(d+X)≤F.t at endpoint
    change F.t+2*Y+d≤R.capacity+1 at space
    change originalThresholdCount F.n x≤X at rn
    change originalThresholdCount F.m y≤Y at bm
    have need : 2*widthAt F.n F.m F.r 10+2*X+2*d+2*q≤R.roots.ncard+2*R.capacity := by
      dsimp only [q];omega
    exact need.trans (by dsimp only [TenBlockPartition.jointPrice];omega)

#print axioms ten_large_top_extra_or_blue_difference
end JSP452Audit.StarHost
