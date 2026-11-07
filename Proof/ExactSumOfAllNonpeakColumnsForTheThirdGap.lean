import ProtectAllHeadsOfFourOrMoreInOneThirdGapList
namespace JSP452Audit.StarHost
theorem third_nonpeak_fee_sum (D H Z N:ℕ) (head:8≤H) (gap:H+3≤D) (ratio:11*N≤24*Z) :
    (∑j∈Finset.range D,thirdColumnFee Z N H j)+3*(N/5)=
      (H+1)*Z+2*(N/3+N/4)+(D-H-2)*(N/5) := by
  let f := thirdColumnFee Z N H
  have cut0 : (∑j∈Finset.range 3,f j)+3*(N/5)=4*Z+(N/3+N/4) := by
    dsimp only [f]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,thirdColumnFee]
    norm_num;omega
  have middle : (∑j∈Finset.range (H-3),f (3+j))=(H-3)*Z := by
    calc
      _ = ∑_j∈Finset.range (H-3),Z := by
        apply Finset.sum_congr rfl;intro j hj
        have inside := Finset.mem_range.mp hj
        dsimp only [f,thirdColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have early : (∑j∈Finset.range H,f j)+3*(N/5)=(H+1)*Z+(N/3+N/4) := by
    have s := Finset.sum_range_add f 3 (H-3)
    rw [show 3+(H-3)=H by omega,middle] at s
    have join : 4*Z+(H-3)*Z=(H+1)*Z := by rw [←Nat.add_mul];congr 1;omega
    omega
  have firstThree (j:ℕ) (atMost:j<2) : f (H+j)=N/(j+3) := by
    dsimp only [f,thirdColumnFee]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
  have three : (∑j∈Finset.range 2,f (H+j))=(N/3+N/4) := by
    apply Eq.trans (Finset.sum_congr rfl (fun j hj => firstThree j (Finset.mem_range.mp hj)))
    norm_num [Finset.sum_range_succ]
  have tail : (∑j∈Finset.range (D-H-2),f (H+2+j))=(D-H-2)*(N/5) := by
    calc
      _ = ∑_j∈Finset.range (D-H-2),N/5 := by
        apply Finset.sum_congr rfl;intro j _
        dsimp only [f,thirdColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have add := Finset.sum_range_add f H 2
  have all := Finset.sum_range_add f (H+2) (D-H-2)
  rw [show H+2+(D-H-2)=D by omega,tail] at all
  rw [three] at add
  change (∑j∈Finset.range D,f j)+_ = _
  omega


#print axioms third_nonpeak_fee_sum
end JSP452Audit.StarHost
