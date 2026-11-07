import ChargeTheTwoMiddleGapsUsingOneFixedAllowance
namespace JSP452Audit.StarHost

def threeSmallCaps (N:ℕ) := N/3+N/4+N/5

theorem middle_fee_sum (D H Z N:ℕ) (head:8≤H) (gap:H+6≤D) (ratio:7*N≤15*Z) :
    (∑j∈Finset.range (D+1),middleColumnFee Z N H j)+4*(N/6)=
      (H+1)*Z+2*threeSmallCaps N+(D-H-2)*(N/6) := by
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
  have tail : (∑j∈Finset.range (D-H-2),f (H+3+j))=(D-H-2)*(N/6) := by
    calc
      _ = ∑_j∈Finset.range (D-H-2),N/6 := by
        apply Finset.sum_congr rfl;intro j _
        dsimp only [f,middleColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have add := Finset.sum_range_add f H 3
  have all := Finset.sum_range_add f (H+3) (D-H-2)
  rw [show H+3+(D-H-2)=D+1 by omega,tail] at all
  rw [three] at add
  change (∑j∈Finset.range (D+1),f j)+_ = _
  omega

theorem middle_fee_pays_whole_gap (D H Z N i:ℕ) (head:8≤H) (gap:H+6≤D) (ratio:7*N≤15*Z) (spent:i≤N/6) :
    (∑j∈Finset.range (D+1),middleColumnFee Z N H j)+(D-H-2)*i≤D*Z := by
  let l := N/6
  let g := D-H-6
  have sum := middle_fee_sum D H Z N head gap ratio
  change _+4*l=(H+1)*Z+2*threeSmallCaps N+(D-H-2)*l at sum
  have cap : l+i≤Z := by dsimp only [l];omega
  have small : 2*threeSmallCaps N+4*l≤5*Z := by dsimp only [l,threeSmallCaps];omega
  have extra := Nat.mul_le_mul_left g cap
  have δ : D-H-2=4+g := by dsimp only [g];omega
  have eq : D*Z=(H+1)*Z+5*Z+g*Z := by rw [←Nat.add_mul,←Nat.add_mul];congr 1;dsimp only [g];omega
  rw [δ,Nat.add_mul 4 g l] at sum
  rw [δ,Nat.add_mul 4 g i,eq]
  rw [Nat.mul_add] at extra
  change i≤l at spent
  omega

#print axioms middle_fee_sum
#print axioms middle_fee_pays_whole_gap
end JSP452Audit.StarHost
