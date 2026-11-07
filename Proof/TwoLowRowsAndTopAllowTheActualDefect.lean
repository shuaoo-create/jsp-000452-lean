import TheBlueHeadBoundaryAndTheMatchingAxisOnBothGraphs
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem low_pair_and_top_with_core_defect (t r a μ u δ d ρ h X Y q g₂ g₃ w₂ w₃ wD c₂ c₃ cD A₂ A₃ : ℕ)
    (rho : h≤ρ) (deficit : ρ≤d+1) (red : a+r+2*(d+X)≤t)
    (embed : t+d+2*Y≤μ+1) (qdef : q=μ-(t+2*Y)+1)
    (blueCount : g₂≤t) (sorted : g₃≤g₂) (mass : t+g₂+d≤μ+a+ρ)
    (outside : a+r+2*(d+Y)+δ≤u) (volume : μ+r+2*d+2*Y≤2*u+2*δ+ρ)
    (base : 2*wD+2*X+2*d≤cD) (fee : a+2*μ≤cD)
    (top : 2*wD+2*X+2*d+2*q≤cD ∨ 2*wD+2*g₃≤2*h+2*g₂)
    (two : 2*w₂≤c₂+A₂ ∨ (2*w₂+2*(u+δ+g₂)≤c₂+2*t ∧ 2*w₂≤c₂+2*q))
    (three : 2*w₃≤c₃+A₃ ∨ 2*w₃+2*(u+δ+g₃)≤c₃+2*g₂) :
    2*w₂+2*w₃+2*wD+2*X+2*d≤c₂+c₃+cD+A₂+A₃+2*ρ+4 := by
  rcases two with plain₂|mix₂ <;> rcases three with plain₃|mix₃ <;> rcases top with hh|b₂ <;> omega


#print axioms low_pair_and_top_with_core_defect
end JSP452Audit.StarHost
