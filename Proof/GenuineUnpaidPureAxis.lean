import FoldThreeActualBoundaryHeights
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def UnpaidPureFromThree {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) : Prop :=
  ∃j,3≤j ∧ j≤D ∧ UnpaidHeight G K n m r j ∧ WinsHeight n m r j j 1

theorem only_two_under_no_pure {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (ht : 0<t) (kinds : SingleUnpaidKinds G K n m ht r)
    (none : ¬UnpaidPureFromThree G K n m r) (j : ℕ) (lo : 2≤j) (hi : j≤D) (bad : UnpaidHeight G K n m r j)
    {x y:ℕ} (win : WinsHeight n m r j x y) :
    x=2 ∧ y=j-1 ∧ (j=2 ∨ j=3 ∨ j=m ⟨0,ht⟩+1) := by
  have ht' := win.2.2.1
  rcases kinds j x y bad win with ⟨ey,ex⟩|⟨ex,_,types⟩
  · subst x;subst y
    have j2 : j=2 := by by_contra not2;exact none ⟨j,by omega,hi,bad,win⟩
    exact ⟨j2,by omega,Or.inl j2⟩
  · rcases types with ⟨_,eq⟩|⟨_,eq⟩ <;> exact ⟨ex,by omega,by omega⟩

theorem actual_pure_axis_needed {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (deg : 6≤D) (cap : ∀z,Nat.card (G.neighborSet z)≤D)
    (top : diagonal n m (r+2)=D+1) (head : n ⟨0,hs⟩=D) (large : 3≤m ⟨0,ht⟩) (sub : m ⟨0,ht⟩<D)
    (d : ℕ) (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+
      (matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s) (inner : t≤matchingEdges (G.induce K.core))
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (kinds : SingleUnpaidKinds G K n m ht r) (missing : MissingHeightWitness G K n m r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r)) :
    UnpaidPureFromThree G K n m r := by
  by_contra none
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let ρ := minimumExposure G D
  let W := componentBudget (G.induce K.core) n
  let δ := μ-W.loss
  let f := originalThresholdCount n 2
  let u := s-f
  let V := μ-f
  let v := originalThresholdCount (W.entries n) 2
  let b := m ⟨0,ht⟩
  let L := widthAt n m r
  let C := basicCapacity G K n m r
  change 3≤b at large;change b<D at sub
  change μ<s at esc;change t≤μ at inner
  change highestWidth n m r≤ρ at width;change ρ+1≤d at reserve
  change a+r+2*(d+∑j,(m j-1)/2)+δ≤s-μ at guard
  have classify (j:ℕ) (lo:2≤j) (hi:j≤D) (gap:C j<2*L j) :
      WinsHeight n m r j 2 (j-1) ∧ (j=2 ∨ j=3 ∨ j=b+1) := by
    obtain ⟨x,y,xp,yp,xy,nx,my,w⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j)
      (by change 0<L j;omega)
    have win : WinsHeight n m r j x y := ⟨xp,yp,xy,nx,my,w⟩
    obtain ⟨ex,ey,kind⟩ := only_two_under_no_pure G K n m ht kinds none j lo hi gap win
    subst x;subst y;exact ⟨win,kind⟩
  obtain ⟨z,lo,hi,bad,_,lost⟩ := missing
  have shape := classify z lo hi bad
  have few := (lost 2 (z-1) shape.1).2.2.1
  change f≤μ at few
  have volume := removal_volume_guard G K n pn
  change μ≤u+a+ρ+3*δ at volume
  have slots (empty:v=0) : μ≤3*V+a+ρ := unit_residual_nonunit_volume G K n hn esc empty
  have tail : V+a+r+2*d+δ≤u := by dsimp only [u,V];omega
  have full := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have opp := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by change 2≤b;omega)
  have p2 := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) full opp
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  have budget : (∑i,(n i-1)/2)+originalThresholdCount m 2≤t := by omega
  obtain ⟨j,y,ypos,level,jhi,posB,over,blue,_last⟩ := trigger
  obtain ⟨yb,jb⟩ := _last few
  change y=b at yb;change j=b+1 at jb
  have win := strict_mixed_layer_exact hs ht n m hn hm pn pm ypos level (actual_height_positive n m live top j (by omega))
    (by omega) budget over blue p2 posB
  rw [yb,jb] at win
  change L (b+1)=f+originalThresholdCount m b-1-r at win
  have present := actual_height_positive n m live top (b+1) (by omega)
  change 0<L (b+1) at present
  have basic : a+2*μ≤C (b+1) := by dsimp [C,basicCapacity,a,μ];omega
  have topfee : 2*L (b+1)+a+2*V+2*r+2≤C (b+1)+2*originalThresholdCount m b := by dsimp only [V];omega
  have endCount := large_opposite_prefix_before_offset hs n m hm head top large
  have ord1 := threshold_anti_height m large
  have ord2 := threshold_anti_height m (show 2≤3 by decide)
  have ord3 := original_threshold_le_length m 2
  have cnt (j:ℕ) (hi:j≤b) : 0<originalThresholdCount m j := (original_threshold_prefix m hm j ⟨0,ht⟩).1 hi
  have triple := last_boundary_three_price t r a μ V v u δ d ρ (highestWidth n m r) (D*ρ)
    (originalThresholdCount m 2) (originalThresholdCount m 3) (originalThresholdCount m b)
    (L 2) (L 3) (L (b+1)) (C 2) (C 3) (C (b+1)) width reserve (by omega) ⟨ord1,ord2,ord3⟩ inner
    (Nat.mul_le_mul_right ρ deg) volume tail slots topfee
  have paidTriple : 2*L 2+2*L 3+2*L (b+1)+2*highestWidth n m r≤C 2+C 3+C (b+1)+D*ρ+2*δ := by
    apply triple
    · intro gap
      have pay := raw_two_head_fee G K n m r 2 1 hn hm pn esc (cnt 2 (by omega)) (classify 2 (by decide) (by omega) gap).1
        (actual_height_positive n m live top 2 (by omega)) few
      rw [original_threshold_one m pm] at pay
      simpa only [Nat.add_assoc] using pay
    · intro gap
      simpa only [Nat.add_assoc] using (raw_two_head_fee G K n m r 3 2 hn hm pn esc (cnt 3 large)
        (classify 3 (by decide) (by omega) gap).1 (actual_height_positive n m live top 3 (by omega)) few)
  have rest (j:ℕ) (lo:4≤j) (hi:j≤D) (away:j≠b+1) : 2*L j≤C j := by
    by_contra! gap;rcases (classify j (by omega) hi gap).2 with x|x|x <;> omega
  have all := fold_any_three_heights D b (highestWidth n m r) ρ δ L C large sub paidTriple rest
  have strict := raw_strict_joint_total G K n m r (rowCount s t r) d hs ht hn hm pn pm (by omega) top rfl esc cap data
  change 2*interiorArea n m r D+2*highestWidth n m r≤(∑z∈Finset.range (D-1),C (z+2))+D*ρ+2*δ at all
  change (∑z∈Finset.range (D-1),C (z+2))+D*ρ+2*δ<2*interiorArea n m r D+2*highestWidth n m r at strict
  omega

#print axioms only_two_under_no_pure
#print axioms actual_pure_axis_needed
end JSP452Audit.StarHost