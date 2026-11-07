import QuinticBoundaryPrefixCaps
namespace JSP452Audit.StarHost

theorem quintic_quaternary_energy (a μ N NB e eB E h ρ ζ β V w2 w3 w4 w5 u2 u3 u4 u5 : ℕ)
    (rank : N≤NB+a+μ) (edge : 2*e+ζ=10*(a+μ)+5*ρ+β+2*eB)
    (width : 1≤h ∧ h≤ρ) (root : 3*ρ+ζ≤10) (slot : 5*ρ+ζ≤5*V)
    (orig : E≤N+w2+w3+w4+w5+h) (ext : NB+u2+u3+u4+u5≤eB)
    (w2p : w2≤a+μ+u2) (w3p : w3≤a+μ+u3) (w4p : w4≤a+μ+u4) (w5p : w5≤a+μ+u5)
    (gain : w3+V≤a+μ+u3 ∨ w4+V≤a+μ+u4 ∨ w5+V≤a+μ+u5) : E≤e := by
  have credit : ζ+2*h≤5*ρ+2*V := by omega
  rcases gain with g|g|g <;> omega

theorem quintic_ternary_middle (M V F w3 w4 u3 u4 : ℕ)
    (four : w4≤M+u4) (three : 2*w3≤2*(M+u3)+F)
    (gain : w3+V≤M+u3 ∨ w4+V≤M+u4) :
    2*(w3+w4)+2*V≤2*(2*M+u3+u4)+F := by rcases gain with g|g <;> omega

theorem quintic_ternary_energy (a μ N k d e eB E h ρ ζ β V F t w2 w3 w4 w5 u2 u3 u4 u5 : ℕ)
    (rank : N=a+μ+k+d) (edge : 2*e+ζ=10*(a+μ)+5*ρ+β+2*eB)
    (width : 1≤h ∧ h≤ρ) (reserve : ρ+1≤d) (inner : t+d≤μ+1) (endp : a+2*(d+F)≤t)
    (root : 3*ρ+ζ≤10) (degree : ζ≤5*a) (volume : μ≤3*V+a+ρ)
    (orig : E≤N+w2+w3+w4+w5+h) (ext : k+u2+u3+u4+u5≤eB)
    (two : w2≤a+μ+u2) (mid : 2*(w3+w4)+2*V≤2*(2*(a+μ)+u3+u4)+F)
    (last : w5+a+d≤a+μ) : E≤e := by
  have credit : ζ+F≤ρ+2*a+2*V := by
    clear rank edge orig ext two mid last
    by_cases few : a≤1 <;> omega
  linarith only [rank,edge,credit,orig,ext,two,mid,last,width.2,Nat.zero_le ρ,Nat.zero_le β,Nat.zero_le u5]

#print axioms quintic_quaternary_energy
#print axioms quintic_ternary_middle
#print axioms quintic_ternary_energy
end JSP452Audit.StarHost