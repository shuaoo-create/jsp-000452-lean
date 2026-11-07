import FiveBinaryZeroHeightProfile
namespace JSP452Audit.StarHost

/-- The fourth layer is the only one with a possible loss. Count
its cost against the same exterior's four uniform inventory layers. -/
theorem five_binary_single_exterior_price (s t a μ k d N e eB E P A F B c h ρ ζ β w u2 u3 u4 u5 : ℕ)
    (rank : N=a+μ+k+d) (edge : 2*e+ζ=10*(a+μ)+5*ρ+β+2*eB)
    (width : 1≤h ∧ h≤ρ) (reserve : ρ+1≤d) (inner : t+d≤μ+1) (endpoint : a+2*(d+F)≤t)
    (root : 3*ρ+ζ≤10) (degree : ζ≤5*a) (vol : 3*A≤3*c+2*μ+a+ρ)
    (peak : P+B=h+1) (bp : 0<B) (pp : 0<P) (area : E≤N+w+(A+B-1)+(F+t-1)+(P+t-1)+h)
    (second : w≤a+μ+u2) (third : c+B≤u3+1+a) (fourth : 2*(F+t-1)≤2*(a+μ+u4)+F)
    (paid : k+u2+u3+u4+u5≤eB) : E≤e := by
  have room : ζ+F+2*A≤ρ+2*a+2*μ+2*c := by
    clear rank edge peak bp pp area second third fourth paid
    by_cases few : a≤1 <;> omega
  have top : P≤h := by omega
  have nt : 0<t := by omega
  have e3 : A+B-1+1=A+B := by omega
  have e4 : F+t-1+1=F+t := by omega
  have e5 : P+t-1+1=P+t := by omega
  have charge : E+3≤N+w+A+B+F+t+P+t+h := by linarith only [area,e3,e4,e5]
  have cut : 2*(F+t)≤2*(a+μ+u4)+F+2 := by linarith only [fourth,e4]
  linarith only [charge,cut,edge,rank,second,third,paid,room,inner,top,width.2,
    Nat.zero_le β,Nat.zero_le u5]

#print axioms five_binary_single_exterior_price
end JSP452Audit.StarHost