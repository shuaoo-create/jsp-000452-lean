import InterpolateActualEvenCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_original_interpolated_cases (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 8).ncard
    let rho := minimumExposure F.G 8
    (rho=5 → c=5 ∧ 4≤h) ∧ (rho=4 → 3≤c) ∧
    (c=1 → h=1 ∧ rho≤3) ∧ (c=0 → h=1 ∧ rho=3) ∧
    (h≥2 → 2≤c) := by
  intro h c rho
  obtain ⟨hp,le,cl,limit,tally,_,none⟩ := strict_eight_inventory F paid eight
  have price := strict_eight_cut_interpolation F paid eight
  change 3*h≤rho+2*c at price
  change 4*rho+1≤h+12+c at tally
  change 1≤h at hp
  change h≤rho at le
  change c≤rho at cl
  change rho≤5 at limit
  change c=0 → rho≤3 at none
  omega

#print axioms eight_original_interpolated_cases
end JSP452Audit.StarHost
