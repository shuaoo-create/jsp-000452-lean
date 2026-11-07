import StrictQuinticUnitExteriorExcluded
namespace JSP452Audit.StarHost

/-- Every real winner is bounded by the pure red axis, or is exactly
one of the two rectangles that a surviving red nonunit can pay. -/
theorem full_opposite_three_options {s t r j : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (pos : 3≤j) (present : 0<widthAt n m r j)
    (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t) :
    widthAt n m r j≤originalThresholdCount n j+t-1-r ∨
    (0<originalThresholdCount m j ∧ widthAt n m r j=s+originalThresholdCount m j-1-r) ∨
    (0<originalThresholdCount m (j-1) ∧ widthAt n m r j=originalThresholdCount n 2+originalThresholdCount m (j-1)-1-r) := by
  obtain ⟨x,y,px,py,level,_,bpos,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega) present
  by_cases unit : x=1
  · have same : y=j := by omega
    rw [unit,same,original_threshold_one n pn] at eq
    exact Or.inr (Or.inl ⟨same ▸ bpos,eq⟩)
  by_cases other : y=1
  · have same : x=j := by omega
    rw [other,same,original_threshold_one m pm] at eq;exact Or.inl eq.le
  by_cases two : x=2
  · have same : y=j-1 := by omega
    rw [two,same] at eq;exact Or.inr (Or.inr ⟨same ▸ bpos,eq⟩)
  have half := half_extra_pays_large_threshold n (by omega : 3≤x)
  have blue := threshold_anti_height m (by omega : 2≤y)
  exact Or.inl (by omega)

theorem strict_mixed_layer_exact {s t r j y : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (pos : 2≤y) (level : y+1=j) (present : 0<widthAt n m r j) (before : r<t)
    (budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t)
    (red : originalThresholdCount n j+t<originalThresholdCount n 2+originalThresholdCount m y)
    (blue : j≤m ⟨0,ht⟩ → s+originalThresholdCount m j<originalThresholdCount n 2+originalThresholdCount m y)
    (px : 0<originalThresholdCount n 2) (py : 0<originalThresholdCount m y) :
    widthAt n m r j=originalThresholdCount n 2+originalThresholdCount m y-1-r := by
  have lower := actual_rectangle_le_column (r:=r) n m hn hm (a:=2) (b:=y) (h:=j) (by omega) px py
  rcases full_opposite_three_options hs ht n m hn hm pn pm (by omega : 3≤j) present budget with axis|⟨gp,ae⟩|⟨_,eq⟩
  · omega
  · have high := (original_threshold_prefix m hm j ⟨0,ht⟩).2 gp
    have cut := blue high;omega
  · simpa [show j-1=y by omega] using eq

theorem above_top_prefix_sum {s t r D x y : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (top : diagonal n m (r+2)=D+1)
    (high : D+1<x+y-1) (rx : 0<originalThresholdCount n x) (by' : 0<originalThresholdCount m y) :
    originalThresholdCount n x+originalThresholdCount m y≤r+1 := by
  have lower := actual_rectangle_le_column (r:=r) n m hn hm rfl rx by'
  have no : offsetsAt n m r (x+y-1)=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k mem
    obtain ⟨inR,htax⟩ := Finset.mem_filter.mp mem
    have bound := Finset.mem_range.mp inR
    have small := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+k by omega)
      (by dsimp [rowCount] at bound;omega)
    omega
  change originalThresholdCount n x+originalThresholdCount m y-1-r≤(offsetsAt n m r (x+y-1)).card at lower
  rw [no,Finset.card_empty] at lower;omega

#print axioms full_opposite_three_options
#print axioms strict_mixed_layer_exact
#print axioms above_top_prefix_sum
end JSP452Audit.StarHost