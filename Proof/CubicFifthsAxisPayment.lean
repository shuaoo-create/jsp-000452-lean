import CubicHalfBudgetIsolation
namespace JSP452Audit.StarHost

/-- In the last full corner i=min(r,f-1), a cubic two-fifths
domination price and the two-neighbour isolation mass pay the exact axis. -/
theorem cubic_fifths_axis_payment (s t r a μ M k z β L ρ h d V f i E e : ℚ)
    (mass : M=a+μ) (rank : M+k+d=s+t-r-1) (exposed : 1≤ρ) (small : ρ≤2)
    (width : h≤ρ) (deficit : ρ+1≤d) (budget : 3*ρ+L≤2*h+2)
    (leaf : V≤s+f) (unused : 2*V≤M+a-s+2*ρ-3*d+1) (tail : t+d≤μ+1)
    (full : 1≤f) (fcap : f≤r+h) (corner : i=r ∨ i=f-1)
    (dom : 10*(t-r+i)≤8*M+4*ρ+5*z+5*β)
    (axis : E≤3*(t-r-1)+s+V+h) (edge : 6*M+3*ρ+2*k+2*z+2*β≤2*e+L)
    (a0 : 0≤a) (k0 : 0≤k) (r0 : 0≤r) (z0 : 0≤z) (β0 : 0≤β) : E≤e := by
  rcases corner with eq|eq
  · linarith only [mass,rank,exposed,small,width,deficit,budget,leaf,unused,tail,full,fcap,eq,dom,axis,edge,a0,k0,r0,z0,β0]
  · linarith only [mass,rank,exposed,small,width,deficit,budget,leaf,unused,tail,full,fcap,eq,dom,axis,edge,a0,k0,r0,z0,β0]

#print axioms cubic_fifths_axis_payment
end JSP452Audit.StarHost
