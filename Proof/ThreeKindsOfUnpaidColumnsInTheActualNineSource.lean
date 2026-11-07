import ShapeOfEveryUnpaidSingleShortNineColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_single_short_unpaid_kinds (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) :
    ∀j x y,R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j →
      WinsHeight F.n F.m F.r j x y →
      (y=1 ∧ x=j) ∨
      (x=2 ∧ (∑i,(F.n i-1)/2)<originalThresholdCount F.n 2 ∧
        ((y=2 ∧ j=3) ∨ (y=F.m ⟨0,F.ht⟩ ∧ j=F.m ⟨0,F.ht⟩+1))) := by
  let a := R.roots.ncard
  let P := R.totalCapacity
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let W := componentBudget (F.G.induce R.chosen) F.n
  have source := nine_long_side_actual_source_prices F paid nine R long
  have live : 0<W.len := source.1
  have fit : W.loss≤P := source.2.2.1
  have root : 1≤a := R.root_count.1
  have endpoint := (strict_nine_original_root_endpoints F paid nine R).1
  have mass := (strict_nine_short_box_masses F paid nine R).2 short
  have lower : 2≤d := (strict_nine_root_deleted_row F paid nine R).1
  have guard := (nine_long_side_exterior_endpoints F paid nine R long).1
  change a+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t at endpoint
  change (∑j,F.m j)+d≤P+2 at mass
  change a+F.r+2*(d+∑j,(F.m j-1)/2)+(P-W.loss)≤F.s-P at guard
  intro j x y loss win
  by_cases unit : y=1
  · exact Or.inl ⟨unit,by have := win.2.2.1;omega⟩
  have two := budget_single_short_mixed_rectangle a P W fit live F.n F.m F.r d j x y F.hs F.ht F.hn F.hm F.pn F.pm
    endpoint (by omega) (by omega) (by omega) long loss win (by have := win.2.1;omega)
  exact Or.inr ⟨two.1,two.2.1,two.2.2.imp (fun v => ⟨v,by have := win.2.2.1;omega⟩) id⟩

/-- A mixed top with escaping-side head at least three already supplies the
entire original matching deficit plus its half-order cost. -/
theorem strict_nine_single_short_large_top_price (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (short : F.t≤R.totalCapacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 9 x y) :
    2*widthAt F.n F.m F.r 9+2*(∑i,(F.n i-1)/2)+2*(F.rank-matchingEdges F.G-R.rankAllowance)≤
      R.roots.ncard+2*R.totalCapacity := by
  let a := R.roots.ncard
  let P := R.totalCapacity
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let X := ∑i,(F.n i-1)/2
  let Y := ∑j,(F.m j-1)/2
  have endpoint := (strict_nine_original_root_endpoints F paid nine R).1
  have space := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
  have mass := (strict_nine_short_box_masses F paid nine R).2 short
  have reserve : 2≤d := (strict_nine_root_deleted_row F paid nine R).1
  have root : 1≤a := R.root_count.1
  change a+F.r+2*(d+X)≤F.t at endpoint
  change F.t+2*Y+d≤P+1 at space
  change (∑j,F.m j)+d≤P+2 at mass
  obtain ⟨x,y,xlo,ylo,win⟩ := winner
  have shape := win.2.2.1
  have width := win.2.2.2.2.2
  change 2*widthAt F.n F.m F.r 9+2*X+2*d≤a+2*P
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

#print axioms strict_nine_single_short_unpaid_kinds
#print axioms strict_nine_single_short_large_top_price
end JSP452Audit.StarHost
