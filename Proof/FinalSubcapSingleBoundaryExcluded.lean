import LastThreeRawPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The remaining (2,D-1) top cannot pay less than the original row.
Use the actual area account (without subtracting the original deficit)
and one deletion pattern when the exterior residual is purely unit. -/
theorem final_subcap_single_impossible {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (deg : 6≤D) (cap : ∀z,Nat.card (G.neighborSet z)≤D)
    (top : diagonal n m (r+2)=D+1) (boundary : TwoHeadTopBoundary n m ht r D)
    (d : ℕ) (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+
      (matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s) (inner : t≤matchingEdges (G.induce K.core))
    (kinds : SingleUnpaidKinds G K n m ht r) (missing : MissingHeightWitness G K n m r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r)) : False := by
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let ρ := minimumExposure G D
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  let δ := μ-W.loss
  let f := originalThresholdCount n 2
  let u := s-f
  let V := μ-f
  let v := originalThresholdCount (W.entries n) 2
  let b := m ⟨0,ht⟩
  let L := widthAt n m r
  let C := basicCapacity G K n m r
  have bval : b=D-1 := boundary.1
  have fit : W.loss≤μ := component_budget_loss_le _ _
  change μ<s at esc
  change t≤μ at inner
  change a+r+2*(d+∑j,(m j-1)/2)+δ≤s-μ at guard
  change highestWidth n m r≤ρ at width
  change ρ+1≤d at reserve
  have sep : t+r+highestWidth n m r<s := by omega
  obtain ⟨i,j,_,peak⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have mcap : m j≤b := hm (show (⟨0,ht⟩:Fin t) ≤ j from Nat.zero_le _)
  have red3 := (original_threshold_prefix n hn 3 i).1 (by omega)
  have zero := last_boundary_forces_unit_J G K n m hs ht hn hm pn pm live top boundary (by omega) sep kinds missing
  change originalThresholdCount J 2=0 at zero
  have few := (common_threshold_floors n hn pn W a μ 2 fit).2.1
  change f≤μ+originalThresholdCount J 2 at few;rw [zero,Nat.add_zero] at few
  have volume := removal_volume_guard G K n pn
  change μ≤u+a+ρ+3*δ at volume
  have slots (empty : v=0) : μ≤3*V+a+ρ := unit_residual_nonunit_volume G K n hn esc empty
  have tail : V+a+r+2*d+δ≤u := by dsimp only [u,V];omega
  have endCount := (large_blue_peak_prefix hs ht n m hn hm live top (by change b≤D;omega)).trans (Nat.add_le_add_left width r)
  change originalThresholdCount m b≤r+ρ at endCount
  have order1 := threshold_anti_height m (show 3≤b by omega)
  have order2 := threshold_anti_height m (show 2≤3 by decide)
  have order3 := original_threshold_le_length m 2
  have topWin := boundary.2.1.2.2.2.2.2
  change widthAt n m r D=f+originalThresholdCount m (D-1)-1-r at topWin
  rw [←bval] at topWin
  have present := actual_height_positive n m live top D (by omega)
  have basic : a+2*μ≤C D := by dsimp [C,basicCapacity,a,μ];omega
  have topfee : 2*L D+a+2*V+2*r+2≤C D+2*originalThresholdCount m b := by
    change 2*widthAt n m r D+a+2*(μ-f)+2*r+2≤C D+2*originalThresholdCount m b
    omega
  have raw (j:ℕ) (lo:2≤j) (hi:j≤D) (gap : C j<2*L j) :=
    last_boundary_gap_kind G K n m hs ht hn hm pn pm live top boundary (by omega) sep kinds j lo hi gap
  have cnt (j:ℕ) (hi:j≤b) : 0<originalThresholdCount m j := (original_threshold_prefix m hm j ⟨0,ht⟩).1 hi
  have triple := last_boundary_three_price t r a μ V v u δ d ρ (highestWidth n m r) (D*ρ)
    (originalThresholdCount m 2) (originalThresholdCount m 3) (originalThresholdCount m b)
    (L 2) (L 3) (L D) (C 2) (C 3) (C D) width reserve endCount ⟨order1,order2,order3⟩ inner
    (Nat.mul_le_mul_right ρ deg) volume tail slots topfee
  have low₂ (gap : C 2<2*L 2) := (raw 2 (by decide) (by omega) gap).1
  have low₃ (gap : C 3<2*L 3) := (raw 3 (by decide) (by omega) gap).1
  have triplePaid : 2*L 2+2*L 3+2*L D+2*highestWidth n m r≤C 2+C 3+C D+D*ρ+2*δ := by
    apply triple
    · intro gap
      have pay := raw_two_head_fee G K n m r 2 1 hn hm pn esc (cnt 2 (by omega)) (low₂ gap)
        (actual_height_positive n m live top 2 (by omega)) few
      rw [original_threshold_one m pm] at pay
      simpa only [Nat.add_assoc] using pay
    · intro gap
      simpa only [Nat.add_assoc] using (raw_two_head_fee G K n m r 3 2 hn hm pn esc (cnt 3 (by omega)) (low₃ gap)
        (actual_height_positive n m live top 3 (by omega)) few)
  have rest (j:ℕ) (lo:4≤j) (hi:j<D) : 2*L j≤C j := by
    by_contra! gap;have z := (raw j (by omega) hi.le gap).2;omega
  have total := fold_last_three_prices D (highestWidth n m r) ρ δ L C deg triplePaid rest
  have strict := raw_strict_joint_total G K n m r (rowCount s t r) d hs ht hn hm pn pm (by omega) top rfl esc cap data
  change 2*interiorArea n m r D+2*highestWidth n m r≤(∑z∈Finset.range (D-1),C (z+2))+D*ρ+2*δ at total
  change (∑z∈Finset.range (D-1),C (z+2))+D*ρ+2*δ<2*interiorArea n m r D+2*highestWidth n m r at strict
  omega

#print axioms final_subcap_single_impossible
end JSP452Audit.StarHost
