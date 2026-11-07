import UnitLargeOppositeLayerPrice
namespace JSP452Audit.StarHost

/-- Interior layers up to the blue maximum each cost at most the rank
difference. At least one higher layer saves the entire red two-prefix
slack, the root count, and one extra unit. -/
theorem quintic_unit_middle_total (a μ A b C3 C4 C5 u3 u4 u5 : ℕ) (heads : b=3 ∨ b=4) (few : A≤μ) (present : 0<A)
    (p3 : C3≤a+μ+u3) (p4 : 4≤b → C4≤a+μ+u4)
    (l4 : b<4 → C4≤A-1) (l5 : C5≤A-1) :
    C3+C4+C5+(μ-A)+a+1≤3*(a+μ)+u3+u4+u5 := by
  rcases heads with x|x
  · have := l4 (by omega);omega
  · have := p4 (by omega);omega

theorem quintic_unit_large_price (s t r a μ N NB E e eB h ρ ζ β d A B Gb w wB sumHigh extHigh : ℕ)
    (rank : N≤NB+a+μ) (edge : 2*e+ζ=10*(a+μ)+5*ρ+β+2*eB)
    (width : 1≤h ∧ h≤ρ) (reserve : ρ+1≤d) (outside : a+r+2*d≤s-μ)
    (before : r<t) (roots : 3*ρ+ζ≤10) (cap : ζ≤5*a) (fit : A≤μ) (volume : 3*A≤2*μ+a+ρ)
    (over : t<A+Gb) (mono : Gb≤B) (area : E≤N+w+sumHigh+h)
    (middle : sumHigh+(μ-A)+a+1≤3*(a+μ)+extHigh)
    (winner : w=A+t-1-r ∨ w=s+B-1-r) (pay2 : s-μ+B-1-(r+a)≤wB)
    (actual : NB+wB+extHigh≤eB) : E≤e := by
  have len : μ≤s := by omega
  have md : μ-A+A=μ := by omega
  have blue : s+B-1-r≤a+μ+wB := by omega
  have red : A+t-1-r+B+(s-μ)≤A+t+wB+a := by omega
  have rootCredit : ζ+2*h≤5*ρ+2*a+2 := by
    by_cases empty : a=0 <;> omega
  rcases winner with x|y <;> omega

#print axioms quintic_unit_middle_total
#print axioms quintic_unit_large_price
end JSP452Audit.StarHost