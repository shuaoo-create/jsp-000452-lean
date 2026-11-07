import TheSurplusOfTheFixedRegularExit
namespace JSP452Audit.StarHost.TenRegularExit
open SimpleGraph
universe u
variable {F:StrictFamily.{u}} {A:PricedTenMenu F} {inc:ℕ}

theorem seven_exposure (E:TenRegularExit A 7 inc) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (cases:TenRegularCases F A) :
    minimumExposure E.graph 7≤E.surplus+4 := by
  obtain ⟨live,smaller,row,cap,eq,_⟩ := E.exact_row_price paid ten cases (by decide)
  have charge := smaller_row_seven_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ F.rank
    row live smaller paid E.cap cap
  omega

theorem six_exposure (E:TenRegularExit A 6 inc) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (cases:TenRegularCases F A) :
    minimumExposure E.graph 6≤E.surplus+4 := by
  obtain ⟨live,smaller,row,cap,eq,_⟩ := E.exact_row_price paid ten cases (by decide)
  by_cases few:minimumExposure E.graph 6≤3
  · omega
  · have price := six_exposure_three_piece_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ F.rank
      row live smaller.le paid E.cap cap (by omega)
    have width := (widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ 7 row (by decide)).trans
      ((uniformEnvelope_le_deletion E.graph 6 (by decide)).trans (deletionBudget_le_minimumExposure E.graph 6 (by decide) E.cap))
    omega

#print axioms seven_exposure
#print axioms six_exposure
end JSP452Audit.StarHost.TenRegularExit
