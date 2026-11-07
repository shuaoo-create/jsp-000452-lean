import UseTheActualRootShiftInThePointCoverPriceForTheDiagonalBoundary
namespace JSP452Audit.StarHost

theorem third_low_history_sum (H Z:ℕ) (L C:ℕ→ℕ) (tax:ℤ) (full:∀j<H,Z≤C j) (low:L (H+2)≤Z) (low':L (H+3)≤Z)
    (debt:((L (H+2)-C H:ℕ):ℤ)+(L (H+3)-C (H+1):ℕ)+tax≤Z) :
    ((∑j∈Finset.range (H+3),min (2*Z) (L (j+1)):ℕ):ℤ)+tax ≤
      ((H+3)*Z+(∑j∈Finset.range (H+3),min Z (C j)):ℕ) := by
  let a := L (H+2)-C H
  let b := L (H+3)-C (H+1)
  have cap (j:ℕ) (_:j∈Finset.range (H+1)) : min (2*Z) (L (j+1))≤2*Z := Nat.min_le_left _ _
  have base := Finset.sum_le_sum cap
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at base
  have first : (∑j∈Finset.range H,min Z (C j))=H*Z := by
    calc
      _ = ∑_j∈Finset.range H,Z := Finset.sum_congr rfl (fun j hj => min_eq_left (full j (Finset.mem_range.mp hj)))
      _ = _ := by simp
  have spare : L (H+2)≤min Z (C H)+a := by dsimp only [a];omega
  have reserve : L (H+3)≤min Z (C (H+1))+b := by dsimp only [b];omega
  let capsum := ∑j∈Finset.range (H+3),min (2*Z) (L (j+1))
  let income := ∑j∈Finset.range (H+3),min Z (C j)
  have size : capsum≤(H+1)*(2*Z)+min Z (C H)+a+min Z (C (H+1))+b := by
    dsimp only [capsum];rw [Finset.sum_range_succ,Finset.sum_range_succ]
    change (∑j∈Finset.range (H+1),min (2*Z) (L (j+1)))+min (2*Z) (L (H+2))+min (2*Z) (L (H+3))≤_
    omega
  have saved : H*Z+min Z (C H)+min Z (C (H+1)) ≤ income := by
    dsimp only [income];rw [Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,first];omega
  have mult : (H+1)*(2*Z)=(H+3)*Z+H*Z-Z := by
    have eq : (H+1)*(2*Z)+Z=(H+3)*Z+H*Z := by ring
    omega
  have safe : Z≤(H+3)*Z := by have := Nat.mul_le_mul_right Z (show 1≤H+3 by omega);omega
  change (a:ℤ)+b+tax≤Z at debt
  change (capsum:ℤ)+tax≤((H+3)*Z+income:ℕ)
  omega

#print axioms third_low_history_sum
end JSP452Audit.StarHost
