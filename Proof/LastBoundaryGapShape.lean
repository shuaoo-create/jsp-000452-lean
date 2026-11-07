import RawCommonAreaAtBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Blue retains its original positive threshold at all intermediate
levels below D. The (3,D-1) top rectangle prevents any red matching
axis of height at least three from attaining the maximum there. -/
theorem no_pure_axis_at_last_boundary {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (boundary : m ⟨0,ht⟩=D-1) (red3 : 0<originalThresholdCount n 3)
    (separated : t+r+highestWidth n m r<s) (j : ℕ) (high : 3≤j) (inside : j<D) :
    ¬ WinsHeight n m r j j 1 := by
  intro win
  let b := m ⟨0,ht⟩
  have g := (original_threshold_prefix m hm b ⟨0,ht⟩).1 le_rfl
  have fee := actual_rectangle_le_column (r:=r) n m hn hm (a:=3) (b:=b) (h:=D+1)
    (by dsimp [b];omega) red3 g
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at peak;rw [peak] at fee
  have smaller := threshold_anti_height n high
  have blue := (original_threshold_prefix m hm j ⟨0,ht⟩).1 (by omega)
  have units := original_threshold_one n pn
  have positive : 0<originalThresholdCount n 1 := by omega
  have actual := actual_rectangle_le_column (r:=r) n m hn hm (a:=1) (b:=j) (h:=j) (by omega) positive blue
  rw [units] at actual
  have winner := win.2.2.2.2.2
  rw [original_threshold_one m pm] at winner
  have present := actual_height_positive n m live top j (by omega)
  omega

/-- At the last boundary, every raw gap is one of the two low
two-head rectangles or the single top rectangle. -/
theorem last_boundary_gap_kind {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (boundary : TwoHeadTopBoundary n m ht r D) (red3 : 0<originalThresholdCount n 3)
    (separated : t+r+highestWidth n m r<s) (kinds : SingleUnpaidKinds G K n m ht r)
    (j : ℕ) (lo : 2≤j) (hi : j≤D) (gap : basicCapacity G K n m r j<2*widthAt n m r j) :
    WinsHeight n m r j 2 (j-1) ∧ (j=2 ∨ j=3 ∨ j=D) := by
  have bad : UnpaidHeight G K n m r j := gap
  have active : 0<widthAt n m r j := by omega
  obtain ⟨x,y,px,py,h,nx,my,rect⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j) active
  have win : WinsHeight n m r j x y := ⟨px,py,h,nx,my,rect⟩
  by_cases endAt : j=D
  · rw [endAt]
    exact ⟨boundary.2.1,Or.inr (Or.inr rfl)⟩
  rcases kinds j x y bad win with pure|mixed
  · obtain ⟨ey,ex⟩ := pure
    subst y;subst x
    have low : j=2 := by
      by_contra ne
      exact no_pure_axis_at_last_boundary hs ht n m hn hm pn pm live top boundary.1 red3 separated j
        (by omega) (by omega) win
    subst j;exact ⟨win,Or.inl rfl⟩
  · obtain ⟨ex,_,low|last⟩ := mixed
    · obtain ⟨ey,ej⟩ := low
      subst x;subst y;subst j
      exact ⟨win,Or.inr (Or.inl rfl)⟩
    · have eq := boundary.1
      omega

theorem last_boundary_forces_unit_J {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (boundary : TwoHeadTopBoundary n m ht r D) (red3 : 0<originalThresholdCount n 3)
    (separated : t+r+highestWidth n m r<s) (kinds : SingleUnpaidKinds G K n m ht r)
    (missing : MissingHeightWitness G K n m r) :
    originalThresholdCount (commonErasedDemand n (componentBudget (G.induce K.core) n)
      K.roots.ncard (matchingEdges (G.induce K.core))) 2=0 := by
  obtain ⟨j,lo,hi,gap,_,lost⟩ := missing
  have shape := last_boundary_gap_kind G K n m hs ht hn hm pn pm live top boundary red3 separated kinds j lo hi gap
  exact (lost 2 (j-1) shape.1).2.1

#print axioms no_pure_axis_at_last_boundary
#print axioms last_boundary_gap_kind
#print axioms last_boundary_forces_unit_J
end JSP452Audit.StarHost
