import StrictFullUnitUniformGap
namespace JSP452Audit.StarHost

theorem split_actual_endpoints (F : ℕ→ℕ) (D : ℕ) (deg : 3≤D) :
    (∑q∈Finset.range (D-1),F (q+2))=F 2+(∑q∈Finset.range (D-3),F (q+3))+F D := by
  rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ]
  rw [show D-2=(D-3)+1 by omega,Finset.sum_range_succ']
  simp only [Nat.zero_add,show D-3+1+2=D by omega]
  simp only [show ∀q:ℕ,q+1+2=q+3 by omega]
  omega

theorem joint_blue_axis_budget (s l μ a r g ub uz : ℕ) (len : s≤l+μ)
    (left : l+g-1-(r+a)≤ub) (right : l+g-1-r≤uz) :
    2*(s+g-1-r)≤a+2*μ+ub+uz ∧ 2*s+2*g≤a+2*μ+ub+uz+2+2*r := by omega

theorem joint_unit_endpoint_balance (D s t r μ a S V A B h ρ w Q2 L δ : ℕ)
    (degree : 3≤D) (width : h≤ρ) (len : s=μ+S) (outside : a+2*ρ≤S)
    (fit : μ=V+A) (vol : μ≤3*V+a+ρ) (over : t<A+B) (before : r<t)
    (winner : w=A+t-1-r ∨ w=s+B-1-r)
    (blue : 2*(s+B-1-r)≤Q2 ∧ 2*s+2*B≤Q2+2+2*r)
    (last : a+2*V+2≤L) : 2*w+2*h≤Q2+D*ρ+2*δ+L := by
  have multi := Nat.mul_le_mul_right ρ (show 2≤D by omega)
  rcases winner with red|opp <;> omega

/-- Test the two actual endpoints and each intervening layer against
one strict joint budget. The root shortfall cancels in that budget. -/
theorem joint_unit_top_contradiction (D h ρ δ L : ℕ) (C Q : ℕ→ℕ) (deg : 3≤D)
    (strict : (∑z∈Finset.range (D-1),Q (z+2))+D*ρ+2*δ <
      2*(∑z∈Finset.range (D-1),C (z+2))+2*h)
    (middle : ∀j,3≤j → j<D → 2*C j≤Q j) (top : 2*C D+L≤Q D)
    (low : 2*C 2+2*h≤Q 2+D*ρ+2*δ+L) : False := by
  have mid := Finset.sum_le_sum (s:=Finset.range (D-3)) (fun z hz => middle (z+3) (by omega)
    (by have := Finset.mem_range.mp hz;omega))
  rw [←Finset.mul_sum] at mid
  rw [split_actual_endpoints Q D deg,split_actual_endpoints C D deg] at strict
  omega

#print axioms split_actual_endpoints
#print axioms joint_blue_axis_budget
#print axioms joint_unit_endpoint_balance
#print axioms joint_unit_top_contradiction
end JSP452Audit.StarHost