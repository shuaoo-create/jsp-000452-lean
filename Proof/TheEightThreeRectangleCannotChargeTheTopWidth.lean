import ALargeMixedTopForcesAUnitJoinedResidual
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_eight_three_rectangle_absent (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (a b : ℕ)
    (shape : (a=8 ∧ b=3) ∨ (a=3 ∧ b=8)) (red : 0<originalThresholdCount F.n a)
    (blue : 0<originalThresholdCount F.m b) :
    originalThresholdCount F.n a+originalThresholdCount F.m b≤F.r+1 := by
  by_contra! wide
  have typed := typed_width_of_original_rectangle F.G F.n F.m F.hn F.hm red blue F.row
  rcases typed with zero|⟨u,v,hu,hv,eq,force⟩
  · omega
  · have cap (x) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
    have few := (strict_nine_original_peak F paid nine).2.2.2.1
    have alternatives := (nine_uniform_signed_alternatives F.G cap a b u v (by omega) (by omega) (by omega)
      hu hv force).2
    omega

theorem strict_nine_large_top_extra_or_blue_difference (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (short : F.t≤R.totalCapacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 9 x y) :
    let X := ∑i,(F.n i-1)/2
    let Y := ∑j,(F.m j-1)/2
    let d := F.rank-matchingEdges F.G-R.rankAllowance
    let q := R.totalCapacity-(F.t+2*Y)+1
    2*widthAt F.n F.m F.r 9+2*X+2*d+2*q≤R.jointPrice 9 ∨
      widthAt F.n F.m F.r 9+originalThresholdCount F.m 3≤originalThresholdCount F.m 2 := by
  intro X Y d q
  obtain ⟨x,y,xhi,yhi,win⟩ := winner
  have hgt := win.2.2.1
  have count := win.2.2.2.1
  have width := win.2.2.2.2.2
  by_cases two : y=2
  · right
    have eight : x=8 := by omega
    subst y;subst x
    obtain ⟨_,_,_,_,i,j,_,_,_,original,_⟩ := strict_nine_original_peak F paid nine
    have head := (original_threshold_prefix F.m F.hm 3 j).mp (by omega)
    have bound := strict_nine_eight_three_rectangle_absent F paid nine 8 3 (Or.inl ⟨rfl,rfl⟩) count (Nat.zero_lt_of_lt head)
    have sorted := threshold_anti_height F.m (show 2≤3 by decide)
    omega
  · left
    have rn := half_extra_pays_large_threshold F.n xhi
    have bm := half_extra_pays_large_threshold F.m (show 3≤y by omega)
    have endpoint := (strict_nine_original_root_endpoints F paid nine R).1
    have space := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
    have pos : 2≤d := (strict_nine_root_deleted_row F paid nine R).1
    change R.roots.ncard+F.r+2*(d+X)≤F.t at endpoint
    change F.t+2*Y+d≤R.totalCapacity+1 at space
    change originalThresholdCount F.n x≤X at rn
    change originalThresholdCount F.m y≤Y at bm
    have need : 2*widthAt F.n F.m F.r 9+2*X+2*d+2*q≤R.roots.ncard+2*R.totalCapacity := by
      dsimp only [q];omega
    exact need.trans (by dsimp only [NinePortRegion.jointPrice];omega)

#print axioms strict_nine_eight_three_rectangle_absent
#print axioms strict_nine_large_top_extra_or_blue_difference
end JSP452Audit.StarHost
