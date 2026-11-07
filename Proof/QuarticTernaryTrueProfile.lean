import CoreSlotSurplusCharge
namespace JSP452Audit.StarHost

/-- All widths use positive original rectangles. The (4,3) rectangle
would have height six, so even its last index precedes the retained row. -/
theorem quartic_ternary_profile {s t r : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (head : n ⟨0,hs⟩=4) (blue : m ⟨0,ht⟩=3) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=5)
    (guard : originalThresholdCount n 3+originalThresholdCount m 2≤t) :
    let A := originalThresholdCount n 2
    let F := originalThresholdCount n 3
    let P := originalThresholdCount n 4
    let B := originalThresholdCount m 2
    let Q := originalThresholdCount m 3
    let h := highestWidth n m r
    0<P ∧ 0<Q ∧ Q≤r ∧ P≤r+h ∧ F≤r+h ∧
    (widthAt n m r 2=A+t-1-r ∨ widthAt n m r 2=s+B-1-r) ∧
    (widthAt n m r 3=F+t-1-r ∨ widthAt n m r 3=A+B-1-r ∨ widthAt n m r 3=s+Q-1-r) ∧
    (widthAt n m r 4≤P+t-1-r ∨ widthAt n m r 4=A+Q-1-r) ∧
    rowEnergy n m r=rowCount s t r+widthAt n m r 2+widthAt n m r 3+widthAt n m r 4+h := by
  intro A F P B Q h
  have ppos : 0<P := (original_threshold_prefix n hn 4 ⟨0,hs⟩).1 head.ge
  have qpos : 0<Q := (original_threshold_prefix m hm 3 ⟨0,ht⟩).1 blue.ge
  have fpos : 0<F := ppos.trans_le (threshold_anti_height n (show 3≤4 by decide))
  have bpos : 0<B := qpos.trans_le (threshold_anti_height m (show 2≤3 by decide))
  have localTop := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at localTop
  have pbound := actual_rectangle_le_column (r:=r) n m hn hm (a:=4) (b:=2) (h:=5) (by decide) ppos bpos
  have fbound := actual_rectangle_le_column (r:=r) n m hn hm (a:=3) (b:=3) (h:=5) (by decide) fpos qpos
  rw [localTop] at pbound fbound
  change P+B-1-r≤h at pbound;change F+Q-1-r≤h at fbound
  have cut := actual_rectangle_le_column (r:=r) n m hn hm (a:=4) (b:=3) (h:=6) (by decide) ppos qpos
  have zero : widthAt n m r 6=0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro k mem
    obtain ⟨idx,v⟩ := Finset.mem_filter.mp mem
    have small := Finset.mem_range.mp idx
    have upper := earlier_diagonal_dominates hs ht n m hn hm (show r≤r+k by omega)
      (by dsimp [rowCount] at small;omega)
    omega
  rw [zero] at cut;change P+Q-1-r≤0 at cut
  have win (j:ℕ) (lo:0<j) (hi:j≤5) :=
    original_column_real_winner hs ht n m hn hm pn pm lo (actual_height_positive n m live top j hi)
  have oneR := original_threshold_one n pn
  have oneB := original_threshold_one m pm
  refine ⟨ppos,qpos,by omega,by omega,by omega,?_,?_,?_,?_⟩
  · obtain ⟨x,y,xp,yp,htop,_,_,w⟩ := win 2 (by decide) (by decide)
    rcases (show (x=2 ∧ y=1) ∨ (x=1 ∧ y=2) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [oneB] at w;exact Or.inl w
    · rw [oneR] at w;exact Or.inr w
  · obtain ⟨x,y,xp,yp,htop,_,_,w⟩ := win 3 (by decide) (by decide)
    rcases (show (x=3 ∧ y=1) ∨ (x=2 ∧ y=2) ∨ (x=1 ∧ y=3) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [oneB] at w;exact Or.inl w
    · exact Or.inr (Or.inl w)
    · rw [oneR] at w;exact Or.inr (Or.inr w)
  · obtain ⟨x,y,xp,yp,htop,_,yb,w⟩ := win 4 (by decide) (by decide)
    have mb := (original_threshold_prefix m hm y ⟨0,ht⟩).2 yb
    rcases (show (x=4 ∧ y=1) ∨ (x=3 ∧ y=2) ∨ (x=2 ∧ y=3) by omega) with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · rw [oneB] at w;exact Or.inl w.le
    · change widthAt n m r 4=F+B-1-r at w
      change F+B≤t at guard
      exact Or.inl (by omega)
    · exact Or.inr w
  · have area := original_area_by_height hs ht n m hn hm pn pm top (by decide)
    simpa [interiorArea,Finset.sum_range_succ,h,Nat.add_assoc] using area

#print axioms quartic_ternary_profile
end JSP452Audit.StarHost
