import ThreeActualUnpaidShapesOnTheTenDegreeRows
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_single_short_large_top_price (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1) (short : F.t≤R.capacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 10 x y) :
    2*widthAt F.n F.m F.r 10+2*(∑i,(F.n i-1)/2)+2*(F.rank-matchingEdges F.G)≤
      R.roots.ncard+2*R.capacity := by
  let a := R.roots.ncard
  let P := R.capacity
  let d := F.rank-matchingEdges F.G
  let X := ∑i,(F.n i-1)/2
  let Y := ∑j,(F.m j-1)/2
  have endpoint := (ten_common_endpoint_guards F paid R).1
  have space := ((ten_short_core_endpoint F paid R).2 short).2.2
  have mass := (ten_short_core_mass F paid R).2 short
  have reserve : 2≤d := (ten_physical_root_deleted_row F paid R).1
  change a+F.r+2*(d+X)≤F.t at endpoint
  change F.t+2*Y+d≤P+1 at space
  change (∑j,F.m j)+d≤P+a+R.eta at mass
  change R.eta≤d+1 at balanced
  obtain ⟨x,y,xlo,ylo,win⟩ := winner
  have shape := win.2.2.1
  have width := win.2.2.2.2.2
  change 2*widthAt F.n F.m F.r 10+2*X+2*d≤a+2*P
  by_cases two : y=2
  · subst y
    have heavy := twice_five_threshold_below_half F.n (show 5≤x by omega)
    change 2*originalThresholdCount F.n x≤X at heavy
    have blue := units_and_twos_below_mass F.m F.pm
    omega
  · have red := half_extra_pays_large_threshold F.n xlo
    have blue := half_extra_pays_large_threshold F.m (show 3≤y by omega)
    change originalThresholdCount F.n x≤X at red
    change originalThresholdCount F.m y≤Y at blue
    omega

#print axioms ten_single_short_large_top_price
end JSP452Audit.StarHost
