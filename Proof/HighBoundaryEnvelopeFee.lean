import ActualLowBlueRectangleFees
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem pure_axis_in_allowance {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ)
    (high : 3≤j) (wins : WinsHeight n m r j j 1) :
    2*widthAt n m r j≤jointLayerCapacity G K j+axisAllowance G K n m r j := by
  classical
  have eq : axisAllowance G K n m r j=doubleEnvelopeLoss G K n m r j := if_pos ⟨high,wins⟩
  rw [eq]
  change 2*widthAt n m r j≤jointLayerCapacity G K j+(2*widthAt n m r j-jointLayerCapacity G K j);omega

theorem non_twohead_inventory_paid {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d j : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (esc : matchingEdges (G.induce K.core)<s) (lo : 2≤j) (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) (no : ¬∃y,WinsHeight n m r j 2 y) :
    2*widthAt n m r j≤jointLayerCapacity G K j+axisAllowance G K n m r j := by
  by_cases paid : 2*widthAt n m r j≤jointLayerCapacity G K j
  · exact paid.trans (Nat.le_add_right _ _)
  have bad := inventory_gap_implies_unpaid G K n m r N d j ht hn hm pn pm esc (by omega) data (by omega)
  have active : 0<widthAt n m r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j) active
  have win : WinsHeight n m r j x y := ⟨px,py,h,nx,my,eq⟩
  rcases kinds j x y bad win with pure|two
  · obtain ⟨e,f⟩ := pure;subst y;subst x
    have hi : 3≤j := by
      by_contra! low
      obtain rfl : j=2 := by omega
      exact no ⟨1,win⟩
    exact pure_axis_in_allowance G K n m r j hi win
  · exact (no ⟨y,two.1 ▸ win⟩).elim

/-- At most one higher mixed level can need an extra allowance. The
peak rectangle bounds the entire class of maximum opposite heads. -/
theorem upper_mixed_boundary_paid {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d j : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (esc : matchingEdges (G.induce K.core)<s) (high : 4≤j) (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r))
    (few : originalThresholdCount n 2≤matchingEdges (G.induce K.core))
    (peak : originalThresholdCount m (m ⟨0,ht⟩)≤r+minimumExposure G D) :
    2*widthAt n m r j≤jointLayerCapacity G K j+axisAllowance G K n m r j+
      (if j=m ⟨0,ht⟩+1 then 2*minimumExposure G D else 0) := by
  by_cases paid : 2*widthAt n m r j≤jointLayerCapacity G K j
  · omega
  have bad := inventory_gap_implies_unpaid G K n m r N d j ht hn hm pn pm esc (by omega) data (by omega)
  have active : 0<widthAt n m r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j) active
  have win : WinsHeight n m r j x y := ⟨px,py,h,nx,my,eq⟩
  rcases kinds j x y bad win with pure|mixed
  · obtain ⟨e,f⟩ := pure;subst y;subst x
    exact (pure_axis_in_allowance G K n m r j (by omega) win).trans (Nat.le_add_right _ _)
  obtain ⟨two,_,low|top⟩ := mixed
  · omega
  obtain ⟨yb,jb⟩ := top
  rw [if_pos jb];rw [two,yb] at eq
  unfold jointLayerCapacity
  omega

theorem large_blue_peak_prefix {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (bcap : m ⟨0,ht⟩≤D) : originalThresholdCount m (m ⟨0,ht⟩)≤r+highestWidth n m r := by
  obtain ⟨i,k,idx,att⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  let b := m ⟨0,ht⟩
  let x := D+2-b
  have mcap : m k≤b := hm (show (⟨0,ht⟩:Fin t) ≤ k from Nat.zero_le _)
  have red : 0<originalThresholdCount n x := by
    have enough : x≤n i := by dsimp [x,b] at *;omega
    have yes := (original_threshold_prefix n hn x i).1 enough
    omega
  have blue : 0<originalThresholdCount m b := (original_threshold_prefix m hm b ⟨0,ht⟩).1 le_rfl
  have bound := actual_rectangle_le_column (r:=r) n m hn hm (a:=x) (b:=b) (h:=D+1)
    (by dsimp [x,b];omega) red blue
  have eq := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at eq;rw [eq] at bound
  change originalThresholdCount m b≤r+highestWidth n m r;omega

#print axioms non_twohead_inventory_paid
#print axioms upper_mixed_boundary_paid
#print axioms large_blue_peak_prefix
end JSP452Audit.StarHost
