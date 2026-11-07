import ThreeSharpDifferentPricesAtTheLastThreeNonpeakColumns
namespace JSP452Audit.StarHost

theorem three_nonpeak_area (D Z c:ℕ) (degree:11≤D) (few:11*c≤2*Z) (A B:ℕ→ℕ)
    (each:∀j<D-1,64*A j≤64*B j+64*Z+(if j=1 then 32*c else 0))
    (last:∀j<D-1,D-4≤j → 64*A j≤64*B j+46*Z ∧
      (D-3≤j → 64*A j≤64*B j+40*Z) ∧ (D-2≤j → 64*A j≤64*B j+36*Z)) :
    2*Z+∑j∈Finset.range (D-1),A j≤D*Z+∑j∈Finset.range D,B j := by
  let d := D-1
  have atLevel (j:ℕ) (hj:j∈Finset.range d) :
      64*A j+(if d-3≤j then 18*Z else 0)+(if d-2≤j then 6*Z else 0)+(if d-1≤j then 4*Z else 0)
        ≤64*B j+64*Z+(if j=1 then 32*c else 0) := by
    have inside := Finset.mem_range.mp hj
    by_cases high:d-3≤j
    · obtain ⟨a,b,c⟩ := last j inside (by dsimp only [d] at high;omega)
      dsimp only [d] at *;split_ifs <;> omega
    · simpa only [if_neg high,if_neg (show ¬d-2≤j by omega),if_neg (show ¬d-1≤j by omega),Nat.add_zero] using each j inside
  have sum := Finset.sum_le_sum atLevel
  have big : 3≤d := by dsimp only [d];omega
  have except : (∑j∈Finset.range d,(if j=1 then 32*c else 0))=32*c := by simp [show 1<d by omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,last_terms_of_range d 3 _ (by omega),
    last_terms_of_range d 2 _ (by omega),last_terms_of_range d 1 _ (by omega),except,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at sum
  norm_cast at sum
  have mul : D*Z=d*Z+Z := by rw [←Nat.succ_mul];congr 1;dsimp only [d];omega
  have extend : (∑j∈Finset.range d,B j)≤∑j∈Finset.range D,B j :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _)) (fun _ _ _ => Nat.zero_le _)
  change 2*Z+∑j∈Finset.range d,A j≤_
  omega

#print axioms three_nonpeak_area
end JSP452Audit.StarHost
