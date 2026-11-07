import FullHeadAxisProfile
import DominatingBlueEndpoint
namespace JSP452Audit.StarHost

/-- Real-valued certificate for the double embedded original row. The
exterior-edge excess cancels with its own coefficient. -/
theorem large_degree_dominating_account (D E e M μ k z ζ β ρ h t r d u v : ℚ)
    (large : 8≤D) (mu0 : 0≤μ) (sub : μ≤M) (k0 : 0≤k) (r0 : 0≤r) (d0 : 0≤d)
    (rho0 : 0≤ρ) (width : h≤ρ) (red : u+d≤M+ρ) (blue : v+d≤M+ρ)
    (energy : E+t≤(t-1-r)*D+u+v+h)
    (edges : 2*e+ζ=2*D*M+D*ρ+β+2*(k+z))
    (cost : D*ρ+ζ+β≤2*μ)
    (dom : (D-1)*(t-r)≤(D-1)*(2*M+ρ)/3+z+β) : E≤e := by
  have surplus : 2*(D-4)*M+(D-10)*ρ-3*(ζ+β)-6*h≥0 := by
    have bigM := mul_nonneg (sub_nonneg.mpr large) (mu0.trans sub)
    have bigρ := mul_nonneg (sub_nonneg.mpr large) rho0
    nlinarith only [bigM,bigρ,cost,width,sub,mu0,rho0]
  nlinarith only [energy,edges,dom,red,blue,surplus,k0,r0,d0,large]

#print axioms large_degree_dominating_account
end JSP452Audit.StarHost
