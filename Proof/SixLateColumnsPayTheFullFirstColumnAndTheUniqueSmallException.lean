import PhysicalPointCoverTaxesAtSmallAndLargeHeadPairs
namespace JSP452Audit.StarHost

theorem six_column_sum (D Z c:ℕ) (degree:8≤D) (few:2*c≤Z) (A B:ℕ→ℕ)
    (each:∀j<D,8*A j≤8*B j+8*Z+(if j=1 then 4*c else 0))
    (last:∀j<D,D-6≤j → 8*A j≤8*B j+5*Z) :
    2*Z+(∑j∈Finset.range D,A j)≤D*Z+(∑j∈Finset.range D,B j) := by
  classical
  have atLevel (j:ℕ) (hj:j∈Finset.range D) :
      8*A j+(if D-6≤j then 3*Z else 0)≤8*B j+8*Z+(if j=1 then 4*c else 0) := by
    have inside := Finset.mem_range.mp hj
    by_cases near:D-6≤j
    · have high := last j inside near
      simp only [if_pos near];omega
    · simpa only [if_neg near,Nat.add_zero] using each j inside
  have sum := Finset.sum_le_sum atLevel
  have late : (∑j∈Finset.range D,(if D-6≤j then 3*Z else 0))=6*(3*Z) := by
    let n := D-6
    change (∑j∈Finset.range D,(if n≤j then 3*Z else 0))=_
    rw [show D=n+6 by dsimp only [n];omega,Finset.sum_range_add]
    have first : (∑j∈Finset.range n,(if n≤j then 3*Z else 0))=0 := by
      apply Finset.sum_eq_zero;intro j hj;rw [if_neg (Nat.not_le.mpr (Finset.mem_range.mp hj))]
    rw [first,Nat.zero_add]
    simp
  have except : (∑j∈Finset.range D,(if j=1 then 4*c else 0))=4*c := by simp [show 1<D by omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,late,except,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
  norm_cast at sum
  omega

#print axioms six_column_sum
end JSP452Audit.StarHost
