import LowPairTopPrice
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The actual top either pays q0 as well, or its width is controlled
by the difference between the opposite two- and three-leaf classes. -/
theorem actual_top_pair_alternative {s t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (top : diagonal n m (r+2)=D+1) (gthree : 0<originalThresholdCount m 3)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (space : t+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)) (dp : 1≤d)
    (win : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y) :
    let μ := matchingEdges (G.induce K.core)
    let X₁ := ∑i,(n i-1)/2
    let Y := ∑j,(m j-1)/2
    let q := μ-(t+2*Y)+1
    2*widthAt n m r D+2*X₁+2*d+2*q≤jointLayerCapacity G K D ∨
      2*widthAt n m r D+2*originalThresholdCount m 3≤2*highestWidth n m r+2*originalThresholdCount m 2 := by
  intro μ X₁ Y q
  obtain ⟨x,y,xhi,yhi,winner⟩ := win
  have height := winner.2.2.1
  have nx := winner.2.2.2.1
  have area := winner.2.2.2.2.2
  by_cases two : y=2
  · right
    subst y
    have peak := actual_rectangle_le_column (r:=r) n m hn hm (a:=x) (b:=3) (h:=D+1) (by omega) nx gthree
    have eq := width_at_actual_top (r:=r) hs ht n m hn hm
    rw [top] at eq;rw [eq] at peak
    have order := threshold_anti_height m (show 2≤3 by decide)
    omega
  · left
    have smallN := half_extra_pays_large_threshold n xhi
    have smallM := half_extra_pays_large_threshold m (by omega : 3≤y)
    change originalThresholdCount n x≤X₁ at smallN
    change originalThresholdCount m y≤Y at smallM
    change K.roots.ncard+r+2*(d+X₁)≤t at endpoint
    change t+2*Y≤μ at space
    have qdef : q=μ-(t+2*Y)+1 := rfl
    have pay : 2*widthAt n m r D+2*X₁+2*d+2*q≤K.roots.ncard+2*μ := by omega
    exact pay.trans (by unfold jointLayerCapacity;omega)

theorem actual_height_positive {s t r D : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1) (j : ℕ) (bound : j≤D+1) :
    0<widthAt n m r j := by
  apply Finset.card_pos.mpr
  exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simpa [top] using bound⟩⟩

/-- Source rows and thresholds for the three-layer arithmetic on the same
graph. The matching-axis allowance for other heights is kept separate. -/
theorem actual_low_top_triple {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (deg : 6≤D) (top : diagonal n m (r+2)=D+1) (blue : 0<originalThresholdCount m 3)
    (d : ℕ) (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (space : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (mass : (∑j,m j)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+
      (matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s) (few : originalThresholdCount n 2≤matchingEdges (G.induce K.core))
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (kinds : SingleUnpaidKinds G K n m ht r) (win : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y) :
    let C := jointLayerCapacity G K
    let A := axisAllowance G K n m r
    2*widthAt n m r 2+2*widthAt n m r 3+2*widthAt n m r D+2*(∑i,(n i-1)/2)+2*d≤
      C 2+C 3+C D+A 2+A 3+2*minimumExposure G D := by
  classical
  intro C A
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let ρ := minimumExposure G D
  let δ := μ-(componentBudget (G.induce K.core) n).loss
  let u := s-originalThresholdCount n 2
  let Y := ∑j,(m j-1)/2
  let q := μ-(t+2*Y)+1
  have dp : 1≤d := by omega
  have room : t+2*Y≤μ := by change t+d+2*Y≤μ+1 at space;omega
  have topPay := mixed_top_surplus G K n m r d pm deg endpoint space mass reserve win
  have topCases := actual_top_pair_alternative G K n m r d hs ht hn hm top blue endpoint room dp win
  have volume := twice_unit_volume G K n pn r d Y few esc guard
  have origCount := units_and_twos_below_mass m pm
  have pre2 := threshold_anti_height m (show 2≤3 by decide)
  have blue2 : 0<originalThresholdCount m 2 := by omega
  have upper := original_threshold_le_length m 2
  have vols : a+r+2*(d+Y)+δ≤u := by
    change originalThresholdCount n 2≤μ at few
    change a+r+2*(d+Y)+δ≤s-μ at guard;dsimp only [u];omega
  apply low_pair_and_top_price t r a μ u δ d ρ (highestWidth n m r) (∑i,(n i-1)/2) Y q
    (originalThresholdCount m 2) (originalThresholdCount m 3) _ _ _ _ _ _ _ _ width reserve endpoint space rfl upper pre2
    (by change (∑j,m j)+d≤μ+a+ρ at mass;omega) vols volume topPay
    (by dsimp [C,jointLayerCapacity,a,μ];omega) topCases
  · by_cases hit : ∃y,WinsHeight n m r 2 2 y
    · obtain ⟨y,winner⟩ := hit
      have edge := winner.2.2.1;have posY := winner.2.1
      have y1 : y=1 := by omega
      subst y
      have low := two_head_internal_fee G K n m r (rowCount s t r) d 2 1 ht hn hm pn pm esc
        (by decide) data blue2 winner (actual_height_positive n m live top 2 (by omega))
      rw [original_threshold_one m pm] at low
      exact Or.inr ⟨low,actual_matching_qbound G K n m ht hn hm pn pm row room 2 (by decide) winner⟩
    · exact Or.inl (non_twohead_inventory_paid G K n m r _ d 2 hs ht hn hm pn pm esc (by decide) kinds data hit)
  · by_cases hit : ∃y,WinsHeight n m r 3 2 y
    · obtain ⟨y,winner⟩ := hit
      have edge := winner.2.2.1
      have y2 : y=2 := by omega
      subst y
      exact Or.inr (two_head_internal_fee G K n m r _ d 3 2 ht hn hm pn pm esc (by decide) data blue winner
        (actual_height_positive n m live top 3 (by omega)))
    · exact Or.inl (non_twohead_inventory_paid G K n m r _ d 3 hs ht hn hm pn pm esc (by decide) kinds data hit)

#print axioms actual_top_pair_alternative
#print axioms actual_low_top_triple
end JSP452Audit.StarHost
