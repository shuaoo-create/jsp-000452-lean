import AllLowerFixedListChargesAtTheActualSevenHeadBoundary
namespace JSP452Audit.StarHost
theorem lower_nonpeak_fee_sum (D H Z N:ℕ) (head:7≤H) (gap:H+4≤D) (ratio:11*N≤24*Z) :
    (∑j∈Finset.range D,middleColumnFee Z N H j)+4*(N/6)=
      (H+1)*Z+2*threeSmallCaps N+(D-H-3)*(N/6) := by
  let f := middleColumnFee Z N H
  have cut0 : (∑j∈Finset.range 4,f j)+4*(N/6)=5*Z+threeSmallCaps N := by
    dsimp only [f,threeSmallCaps]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,middleColumnFee]
    norm_num;omega
  have middle : (∑j∈Finset.range (H-4),f (4+j))=(H-4)*Z := by
    calc
      _ = ∑_j∈Finset.range (H-4),Z := by
        apply Finset.sum_congr rfl;intro j hj
        have inside := Finset.mem_range.mp hj
        dsimp only [f,middleColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have early : (∑j∈Finset.range H,f j)+4*(N/6)=(H+1)*Z+threeSmallCaps N := by
    have s := Finset.sum_range_add f 4 (H-4)
    rw [show 4+(H-4)=H by omega,middle] at s
    have join : 5*Z+(H-4)*Z=(H+1)*Z := by rw [←Nat.add_mul];congr 1;omega
    omega
  have firstThree (j:ℕ) (atMost:j<3) : f (H+j)=N/(j+3) := by
    dsimp only [f,middleColumnFee]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
  have three : (∑j∈Finset.range 3,f (H+j))=threeSmallCaps N := by
    apply Eq.trans (Finset.sum_congr rfl (fun j hj => firstThree j (Finset.mem_range.mp hj)))
    dsimp only [threeSmallCaps];norm_num [Finset.sum_range_succ]
  have tail : (∑j∈Finset.range (D-H-3),f (H+3+j))=(D-H-3)*(N/6) := by
    calc
      _ = ∑_j∈Finset.range (D-H-3),N/6 := by
        apply Finset.sum_congr rfl;intro j _
        dsimp only [f,middleColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have add := Finset.sum_range_add f H 3
  have all := Finset.sum_range_add f (H+3) (D-H-3)
  rw [show H+3+(D-H-3)=D by omega,tail] at all
  rw [three] at add
  change (∑j∈Finset.range D,f j)+_ = _
  omega


#print axioms lower_nonpeak_fee_sum
end JSP452Audit.StarHost
