import FourPureAxisCost
import ActualWinningRectangles
namespace JSP452Audit.StarHost

/-- Leaf mass and legal top-width constraints for a four-leaf original
head. The two-leaf threshold on the opposite side is genuinely inhabited. -/
theorem four_full_head_leaf_terms {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (cap : ∀i,n i≤4) (head : n ⟨0,hs⟩=4) (live : 0<rowCount s t r)
    (top : diagonal n m (r+2)=5) :
    let f := originalThresholdCount n 4
    s≤∑i,n i ∧ (∑i,n i)≤3*s+f ∧ f≤r+highestWidth n m r := by
  intro f
  let B := originalThresholdCount m 2
  have fpos : 0<f := (original_threshold_prefix n hn 4 ⟨0,hs⟩).1 head.ge
  obtain ⟨i,j,idx,atTop⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have capI := cap i
  have b2 : 2≤m j := by omega
  have bj := (original_threshold_prefix m hm 2 j).1 b2
  have bpos : 0<B := by change j.val<B at bj;omega
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (by decide : 4+2-1=5) fpos bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at peak
  rw [peak] at rect
  change f+B-1-r≤highestWidth n m r at rect
  have point (i:Fin s) : n i≤3+(if 4≤n i then 1 else 0) := by
    have hi:=cap i;split_ifs <;> omega
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => point i)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
    Finset.sum_boole,Nat.cast_id] at total
  change (∑i,n i)≤s*3+f at total
  have lower := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => pn i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one] at lower
  exact ⟨lower,by omega,by omega⟩

#print axioms four_full_head_leaf_terms
end JSP452Audit.StarHost
