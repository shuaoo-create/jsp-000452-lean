import ActualSuppressionBothSuccessors
namespace JSP452Audit.StarHost

theorem suppression_base_arithmetic (μ a ρ η : ℕ) (fee : 13*η≤4*(2*μ+a+ρ)) :
    let P := max a (2*μ-(a+2*η))
    5*μ≤17*P+4*ρ ∧ 2*μ≤7*P+2*ρ := by
  intro P
  have one : a≤P := le_max_left _ _
  have two : 2*μ-(a+2*η)≤P := le_max_right _ _
  omega

theorem suppression_pure_axis_price (μ a t r η f w u z : ℕ) (inner : t≤μ) (full : w≤f+t-1-r)
    (ub : t-(r+a+η)≤u) (zb : t-(r+a+η)≤z) :
    2*w+max a (2*μ-(a+2*η))≤a+2*μ+u+z+2*f := by
  rcases le_total a (2*μ-(a+2*η)) with le|le
  · rw [max_eq_right le];omega
  · rw [max_eq_left le];omega

theorem seven_high_payment (D b μ P ρ h d t r a X q : ℕ) (deg : 9≤D) (gap : 7≤D-b-1)
    (base : 2*μ≤7*P+2*ρ) (width : h≤ρ) (pos : 1≤d)
    (rank : q+t=μ+1) (endpoint : a+r+2*(d+X)≤t) :
    q+4*X+2*ρ+2*h+2*d≤(D-b-1)*P+D*ρ := by
  have cols := Nat.mul_le_mul_right P gap
  have res := Nat.mul_le_mul_right ρ deg
  omega

#print axioms suppression_base_arithmetic
#print axioms suppression_pure_axis_price
#print axioms seven_high_payment
end JSP452Audit.StarHost