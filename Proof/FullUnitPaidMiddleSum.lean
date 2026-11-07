import OriginalDegreeFiveExcluded
namespace JSP452Audit.StarHost

/-- Count all heights strictly above the last opposing head, retaining
the first two layers separately and keeping the same exterior row. -/
theorem full_unit_middle_sum (D b M V a : ℕ) (C U : ℕ→ℕ) (hi : b≤D) (lo : 3≤b)
    (low : ∀j,3≤j → j≤b → C j≤M+U j)
    (high : ∀j,b<j → j≤D → C j+(V+a+1)≤M+U j) :
    (∑z∈Finset.range (D-2),C (z+3))+(D-b)*(V+a+1)≤
      (D-2)*M+∑z∈Finset.range (D-2),U (z+3) := by
  let pay (j:ℕ) := if b<j then V+a+1 else 0
  have point (z:ℕ) (mem:z∈Finset.range (D-2)) : C (z+3)+pay (z+3)≤M+U (z+3) := by
    have bound := Finset.mem_range.mp mem
    by_cases above : b<z+3
    · simpa [pay,above] using high (z+3) above (by omega)
    · simpa [pay,above] using low (z+3) (by omega) (by omega)
  have total := Finset.sum_le_sum point
  have count : (∑z∈Finset.range (D-2),pay (z+3))=(D-b)*(V+a+1) := by
    rw [show D-2=(b-2)+(D-b) by omega,Finset.sum_range_add]
    have left : (∑z∈Finset.range (b-2),pay (z+3))=0 := Finset.sum_eq_zero (by
      intro z hz;have := Finset.mem_range.mp hz;simp [pay,show ¬b<z+3 by omega])
    have right (z:ℕ) : pay (b-2+z+3)=V+a+1 := by simp [pay,show b<b-2+z+3 by omega]
    simp [left,right]
  rw [Finset.sum_add_distrib,count,Finset.sum_add_distrib] at total
  simpa using total

theorem interior_peel_two {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r D : ℕ) (large : 2≤D) :
    interiorArea n m r D=widthAt n m r 2+∑z∈Finset.range (D-2),widthAt n m r (z+3) := by
  unfold interiorArea
  rw [show D-1=(D-2)+1 by omega,Finset.sum_range_succ']
  simp [Nat.add_assoc,Nat.add_comm]

#print axioms full_unit_middle_sum
#print axioms interior_peel_two
end JSP452Audit.StarHost