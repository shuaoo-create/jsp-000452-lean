import ThePointCoverRatioAtTwoDifferentMinimumHeadSizes
namespace JSP452Audit.StarHost

theorem last_terms_of_range (D n z:ℕ) (room:n≤D) :
    (∑j∈Finset.range D,if D-n≤j then z else 0)=n*z := by
  let m := D-n
  change (∑j∈Finset.range D,if m≤j then z else 0)=_
  rw [show D=m+n by dsimp only [m];omega,Finset.sum_range_add]
  have first : (∑j∈Finset.range m,if m≤j then z else 0)=0 := by
    apply Finset.sum_eq_zero;intro j hj;rw [if_neg (Nat.not_le.mpr (Finset.mem_range.mp hj))]
  rw [first,Nat.zero_add];simp

theorem five_column_area (D Z c:ℕ) (deg:14≤D) (few:7*c≤Z) (A B:ℕ→ℕ)
    (each:∀j<D,24*A j≤24*B j+24*Z+(if j=1 then 12*c else 0))
    (last:∀j<D,D-5≤j →
      24*A j≤24*B j+16*Z ∧ (D-4≤j → 24*A j≤24*B j+15*Z) ∧ (D-3≤j → 24*A j≤24*B j+13*Z)) :
    2*Z+∑j∈Finset.range D,A j≤D*Z+∑j∈Finset.range D,B j := by
  classical
  have atLevel (j:ℕ) (hj:j∈Finset.range D) :
      24*A j+(if D-5≤j then 8*Z else 0)+(if D-4≤j then Z else 0)+(if D-3≤j then 2*Z else 0)
        ≤24*B j+24*Z+(if j=1 then 12*c else 0) := by
    have inside := Finset.mem_range.mp hj
    by_cases high:D-5≤j
    · obtain ⟨a,b,c⟩ := last j inside high
      split_ifs <;> omega
    · simpa only [if_neg high,if_neg (show ¬D-4≤j by omega),if_neg (show ¬D-3≤j by omega),Nat.add_zero] using each j inside
  have sum := Finset.sum_le_sum atLevel
  have except : (∑j∈Finset.range D,(if j=1 then 12*c else 0))=12*c := by simp [show 1<D by omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,last_terms_of_range D 5 _ (by omega),
    last_terms_of_range D 4 _ (by omega),last_terms_of_range D 3 _ (by omega),except,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
  norm_cast at sum
  omega

#print axioms last_terms_of_range
#print axioms five_column_area
end JSP452Audit.StarHost
