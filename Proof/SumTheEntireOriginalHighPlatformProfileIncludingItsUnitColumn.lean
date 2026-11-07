import ChargeAllHeightPairsOfTheFixedHighPlatformSuccessor
namespace JSP452Audit.StarHost

theorem protected_fee_sum (D H Z N:ℕ) (head:10≤H) (gap:H+8≤D) (ratio:9*N≤19*Z) :
    (∑j∈Finset.range (D+1),protectedColumnFee Z N H j)+N/7≤(H+1)*Z+2*N+(D-H-3)*(N/7) := by
  let f := protectedColumnFee Z N H
  let M := N/3+N/4+N/5+N/6
  have cut0 : (∑j∈Finset.range 5,f j)+N/7=6*Z+M := by
    dsimp only [f,M]
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,protectedColumnFee]
    norm_num;omega
  have middle : (∑j∈Finset.range (H-5),f (5+j))=(H-5)*Z := by
    calc
      _ = ∑_j∈Finset.range (H-5),Z := by
        apply Finset.sum_congr rfl;intro j hj
        have inside := Finset.mem_range.mp hj
        dsimp only [f,protectedColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have early : (∑j∈Finset.range H,f j)+N/7=(H+1)*Z+M := by
    have s := Finset.sum_range_add f 5 (H-5)
    rw [show 5+(H-5)=H by omega,middle] at s
    have join : 6*Z+(H-5)*Z=(H+1)*Z := by rw [←Nat.add_mul];congr 1;omega
    omega
  have firstFour (j:ℕ) (atMost:j<4) : f (H+j)=N/(j+3) := by
    dsimp only [f,protectedColumnFee]
    rw [if_neg (by omega),if_neg (by omega),if_neg (by omega),if_pos (by omega),Nat.add_sub_cancel_left]
  have four : (∑j∈Finset.range 4,f (H+j))=M := by
    apply Eq.trans (Finset.sum_congr rfl (fun j hj => firstFour j (Finset.mem_range.mp hj)))
    dsimp only [M];norm_num [Finset.sum_range_succ]
  have tail : (∑j∈Finset.range (D-H-3),f (H+4+j))=(D-H-3)*(N/7) := by
    calc
      _ = ∑_j∈Finset.range (D-H-3),N/7 := by
        apply Finset.sum_congr rfl;intro j _
        dsimp only [f,protectedColumnFee];split_ifs <;> omega
      _ = _ := by simp
  have add := Finset.sum_range_add f H 4
  have all := Finset.sum_range_add f (H+4) (D-H-3)
  rw [show H+4+(D-H-3)=D+1 by omega,tail] at all
  rw [four] at add
  change (∑j∈Finset.range (D+1),f j)+_≤_
  have cheap : M≤N := by dsimp only [M];omega
  omega

theorem protected_fee_pays_whole_gap (D H Z N i:ℕ) (head:10≤H) (gap:H+8≤D) (ratio:9*N≤19*Z) (spent:i≤N/7) :
    (∑j∈Finset.range (D+1),protectedColumnFee Z N H j)+(D-H-3)*i≤D*Z := by
  let l := N/7
  let g := D-H-8
  have sum := protected_fee_sum D H Z N head gap ratio
  change _+l≤(H+1)*Z+2*N+(D-H-3)*l at sum
  have cap : l+i≤Z := by dsimp only [l];omega
  have small : 2*N+9*l≤7*Z := by dsimp only [l];omega
  have extra := Nat.mul_le_mul_left g cap
  have δ : D-H-3=5+g := by dsimp only [g];omega
  have eq : D*Z=(H+1)*Z+7*Z+g*Z := by rw [←Nat.add_mul,←Nat.add_mul];congr 1;dsimp only [g];omega
  rw [δ,Nat.add_mul 5 g l] at sum
  rw [δ,Nat.add_mul 5 g i]
  rw [Nat.mul_add] at extra
  rw [eq]
  change i≤l at spent
  omega

#print axioms protected_fee_sum
#print axioms protected_fee_pays_whole_gap
end JSP452Audit.StarHost
