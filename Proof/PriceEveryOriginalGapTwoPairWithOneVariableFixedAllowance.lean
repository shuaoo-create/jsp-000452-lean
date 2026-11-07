import EveryOriginalGapTwoWitnessHasOnePayableTwoColumnSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph

def twoColumnFixedFee (Z N H l j:ℕ) : ℕ :=
  if j<H then Z+(if j=0 then Z-l else if j=1 then N/3-l else if j=2 then N/4-l else 0)
  else if j=H then N/3 else l+(N/4-l)

theorem two_column_pair_price (Z N H l j x y:ℕ) (ratio:16*N≤35*Z) (head:9≤H)
    (lo:N/5≤l) (hi:l≤N/3) (px:0<x) (py:0<y) (mx:x≤H) (my:y≤H) (ht:x+y=j+2) (last:j≤H+1) :
    l+fixedHeadLoss Z N l x+fixedHeadLoss Z N l y≤twoColumnFixedFee Z N H l j := by
  have bound (v:ℕ) : fixedHeadLoss Z N l v≤Z-l := by unfold fixedHeadLoss;omega
  have cap (v k:ℕ) (pos:0<k) (ok:k≤v+1) : fixedHeadLoss Z N l v≤N/k-l := by
    have h : N/(v+1)≤N/k := Nat.div_le_div_left ok pos
    unfold fixedHeadLoss;omega
  have slots (v:ℕ) : (2≤v → fixedHeadLoss Z N l v≤N/3-l) ∧
      (3≤v → fixedHeadLoss Z N l v≤N/4-l) ∧ (4≤v → fixedHeadLoss Z N l v=0) := by
    exact ⟨fun h => cap v 3 (by decide) (by omega),fun h => cap v 4 (by decide) (by omega),
      fun h => by have := cap v 5 (by decide) (by omega);omega⟩
  obtain ⟨x2,x3,x4⟩ := slots x
  obtain ⟨y2,y3,y4⟩ := slots y
  have bx := bound x
  have byy := bound y
  unfold twoColumnFixedFee
  split_ifs <;> omega

theorem two_column_price_sum (Z N H l:ℕ) (head:9≤H) (ratio:16*N≤35*Z) (lo:N/5≤l) (hi:l≤N/3) :
    (∑j∈Finset.range (H+2),twoColumnFixedFee Z N H l j)+l=(H+1)*Z+2*(N/3)+2*(N/4-l) := by
  have eq : (∑j∈Finset.range H,twoColumnFixedFee Z N H l j)=
      ∑j∈Finset.range H,(Z+((if j=0 then Z-l else 0)+(if j=1 then N/3-l else 0)+(if j=2 then N/4-l else 0))) := by
    apply Finset.sum_congr rfl
    intro j mem
    have less := Finset.mem_range.mp mem
    simp only [twoColumnFixedFee,if_pos less];split_ifs <;> omega
  rw [show H+2=H+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,eq]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id]
  simp [twoColumnFixedFee,show 0<H by omega,show 1<H by omega,show 2<H by omega,Nat.add_mul]
  <;> omega

#print axioms two_column_pair_price
#print axioms two_column_price_sum
end JSP452Audit.StarHost