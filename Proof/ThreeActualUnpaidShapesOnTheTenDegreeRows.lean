import MixedRectanglesUnderTheTenDegreeShortMass
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_single_short_unpaid_kinds (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (many:1≤R.eta) (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity) :
    ∀j x y,R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j →
      WinsHeight F.n F.m F.r j x y →
      (y=1 ∧ x=j) ∨
      (x=2 ∧ (∑i,(F.n i-1)/2)<originalThresholdCount F.n 2 ∧
        ((y=2 ∧ j=3) ∨ (y=F.m ⟨0,F.ht⟩ ∧ j=F.m ⟨0,F.ht⟩+1))) := by
  let a := R.roots.ncard
  let P := R.capacity
  let d := F.rank-matchingEdges F.G
  let W := componentBudget (F.G.induce R.core) F.n
  have source := ten_long_side_two_prices F paid ten R small many long
  have live : 0<W.len := source.1
  have fit : W.loss≤P := source.2.2.1
  have endpoint := (ten_common_endpoint_guards F paid R).1
  have mass := (ten_short_core_mass F paid R).2 short
  have lower : 2≤d := (ten_physical_root_deleted_row F paid R).1
  have guard := (ten_long_side_exterior_endpoints F paid ten R small many long).1
  change a+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t at endpoint
  change R.eta≤d+1 at balanced
  change (∑j,F.m j)+d≤P+a+R.eta at mass
  change a+F.r+2*(d+∑j,(F.m j-1)/2)+(P-W.loss)≤F.s-P at guard
  intro j x y loss win
  by_cases unit : y=1
  · exact Or.inl ⟨unit,by have := win.2.2.1;omega⟩
  have two := mixed_rectangle_under_defect_mass a P W fit live F.n F.m F.r d j x y F.hs F.ht F.hn F.hm F.pn F.pm
    endpoint (by omega) (by omega) (by omega) long loss win (by have := win.2.1;omega)
  exact Or.inr ⟨two.1,two.2.1,two.2.2.imp (fun v => ⟨v,by have := win.2.2.1;omega⟩) id⟩

#print axioms ten_single_short_unpaid_kinds
end JSP452Audit.StarHost
