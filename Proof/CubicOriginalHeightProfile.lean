import ActualWinningRectangles
import FiveDegreeSelectorCeiling
namespace JSP452Audit.StarHost

/-- Exact total edge demand for a list of stars of at most three leaves. -/
theorem cubic_original_leaf_sum {s : ℕ} (n : Fin s→ℕ) (pos : ∀i,1≤n i) (cap : ∀i,n i≤3) :
    (∑i,n i)=s+originalThresholdCount n 2+originalThresholdCount n 3 := by
  have eq (i : Fin s) : n i=1+(if 2≤n i then 1 else 0)+(if 3≤n i then 1 else 0) := by
    have lo:=pos i;have hi:=cap i;split_ifs <;> omega
  calc
    _ = ∑i:Fin s,(1+(if 2≤n i then 1 else 0)+(if 3≤n i then 1 else 0)) := Finset.sum_congr rfl (fun i _ => eq i)
    _ = _ := by simp [originalThresholdCount,Finset.sum_add_distrib,Finset.sum_boole]

/-- Exact decomposition of a row with first diagonal equal to four. -/
theorem cubic_original_height_profile {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (top : diagonal n m (r+2)=4) :
    rowEnergy n m r=rowCount s t r+widthAt n m r 2+widthAt n m r 3+highestWidth n m r := by
  have cap (k:ℕ) (hk:k<rowCount s t r) : diagonal n m (r+k+2)≤4 := by
    rw [←top];exact earlier_diagonal_dominates hs ht n m hn hm (by omega) (by dsimp [rowCount] at hk;omega)
  have cnt := finite_layer_count (fun k => diagonal n m (r+k+2)) (rowCount s t r) 4 cap
  change rowEnergy n m r=(∑k∈Finset.range 4,widthAt n m r (k+1)) at cnt
  have first : widthAt n m r 1=rowCount s t r := first_layer_complete hs ht n m pn pm r
  have last := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at last
  rw [cnt]
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,Nat.reduceAdd,zero_add,first,last]

private theorem positive_low_column {s t r h : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (live : 0<rowCount s t r) (top : h≤diagonal n m (r+2)) : 0<widthAt n m r h := by
  apply Finset.card_pos.mpr
  exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simpa using top⟩⟩

/-- The height-two and height-three columns have actual positive winners.
The five alternatives exclude all phantom rectangles with an empty side. -/
theorem cubic_original_column_winners {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=4) :
    let A := originalThresholdCount n 2
    let B := originalThresholdCount m 2
    let P := originalThresholdCount n 3
    let Q := originalThresholdCount m 3
    let w := widthAt n m r 2
    let v := widthAt n m r 3
    ((0<A ∧ w=A+t-1-r) ∨ (0<B ∧ w=s+B-1-r)) ∧
      ((0<P ∧ v=P+t-1-r) ∨ (0<A ∧ 0<B ∧ v=A+B-1-r) ∨ (0<Q ∧ v=s+Q-1-r)) := by
  intro A B P Q w v
  have win (h:ℕ) (hp:0<h) (hh:h≤4) := original_column_real_winner hs ht n m hn hm pn pm hp
    (positive_low_column n m live (by omega : h≤diagonal n m (r+2)))
  constructor
  · obtain ⟨a,b,pa,pb,pair,x,y,eq⟩ := win 2 (by decide) (by decide)
    rcases (show (a=2 ∧ b=1) ∨ (a=1 ∧ b=2) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [original_threshold_one m pm] at eq;exact Or.inl ⟨x,eq⟩
    · rw [original_threshold_one n pn] at eq;exact Or.inr ⟨y,eq⟩
  · obtain ⟨a,b,pa,pb,pair,x,y,eq⟩ := win 3 (by decide) (by decide)
    rcases (show (a=3 ∧ b=1) ∨ (a=2 ∧ b=2) ∨ (a=1 ∧ b=3) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [original_threshold_one m pm] at eq;exact Or.inl ⟨x,eq⟩
    · exact Or.inr (Or.inl ⟨x,y,eq⟩)
    · rw [original_threshold_one n pn] at eq;exact Or.inr (Or.inr ⟨y,eq⟩)

#print axioms cubic_original_leaf_sum
#print axioms cubic_original_height_profile
#print axioms cubic_original_column_winners
end JSP452Audit.StarHost
