import LargeDegreeDominatingAccount
namespace JSP452Audit.StarHost

theorem quarter_bound_at_six (D : ℕ) (large : 6≤D) : 1/4+(3/4:ℚ)^(D+1)≤7/18 := by
  have dec := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤3/4) (by norm_num : (3/4:ℚ)≤1)
    (show 7≤D+1 by omega)
  norm_num at dec ⊢;linarith

/-- When the actual weight selector pays at most twelve, the same integer
row constraints force a positive edge margin even at exposure one. -/
theorem middle_degree_dominating_account (D E e M k z ζ β ρ h t r d u v : ℚ)
    (large : 6≤D) (m0 : 0≤M) (k0 : 0≤k) (r0 : 0≤r)
    (exposed : 1≤ρ) (deficit : ρ+1≤d) (width : h≤ρ) (red : u+d≤M+ρ) (blue : v+d≤M+ρ)
    (energy : E+t≤(t-1-r)*D+u+v+h)
    (edges : 2*e+ζ=2*D*M+D*ρ+β+2*(k+z))
    (cost : D*ρ+ζ+β≤2*M) (weight : D*ρ+ζ+β+2≤2*h+24)
    (dom : (D-1)*(t-r)≤(D-1)*(7/18)*(2*M+ρ)+z+β) :
    39*ρ-32≤18*(e-E) := by
  have growthM := mul_nonneg (sub_nonneg.mpr large) m0
  have growthρ := mul_nonneg (sub_nonneg.mpr large) (by linarith : 0≤ρ)
  have bound : 18*(e-E)≥2*M-17*ρ-9*(ζ+β)+18*(2*d+6-h) := by
    nlinarith only [growthM,growthρ,red,blue,energy,edges,dom,large,k0,r0]
  nlinarith only [bound,cost,weight,deficit,width,growthρ]

#print axioms quarter_bound_at_six
#print axioms middle_degree_dominating_account
end JSP452Audit.StarHost
