import FoldLowTopAndBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Any top interior winner with escaping head at least three and
opposite head at least two pays even a completely unit joined residual.
The two low layers, the matching-axis repairs and the single boundary
allowance all refer to these two actual graphs. -/
theorem single_escape_large_top_impossible {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (guard : K.roots.ncard+r+2*(d+∑j,(m j-1)/2)+
      (matchingEdges (G.induce K.core)-(componentBudget (G.induce K.core) n).loss)≤s-matchingEdges (G.induce K.core))
    (space : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (mass : (∑j,m j)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (esc : matchingEdges (G.induce K.core)<s) (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (mc : m ⟨0,ht⟩≤D) (mthree : 0<originalThresholdCount m 3)
    (win : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y) : False := by
  classical
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let ρ := minimumExposure G D
  let X₁ := ∑i,(n i-1)/2
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  let C := jointLayerCapacity G K
  let A := axisAllowance G K n m r
  let L := widthAt n m r
  let b := m ⟨0,ht⟩
  have zero := subcap_nonunit_residual_impossible G K n m hs ht hn hm pn pm row deg cap top d rank strict width
    endpoint space mass reserve esc kinds data win
  have fit : W.loss≤μ := component_budget_loss_le _ _
  have few := (common_threshold_floors n hn pn W a μ 2 fit).2.1
  change originalThresholdCount n 2≤μ+originalThresholdCount J 2 at few
  change originalThresholdCount J 2=0 at zero
  rw [zero,Nat.add_zero] at few
  have triple := actual_low_top_triple G K n m hs ht hn hm pn pm row live deg top mthree d width reserve endpoint space
    mass guard esc few data kinds win
  have peak := (large_blue_peak_prefix hs ht n m hn hm live top mc).trans (Nat.add_le_add_left width r)
  have outside (j:ℕ) (hi:4≤j) (_:j<D) :=
    upper_mixed_boundary_paid G K n m r _ d j hs ht hn hm pn pm esc hi kinds data few peak
  have all : (∑z∈Finset.range (D-1),A (z+2))≤2*X₁ := by
    rw [axis_allowance_sum _ _ _ _ _ (by omega)]
    exact sum_actual_matching_axes G K n m ht hn hm pn pm row (by omega)
  have fold := fold_low_top_boundary D b d ρ X₁ L C A deg triple outside all
  change 2*interiorArea n m r D+2*d≤(∑z∈Finset.range (D-1),jointLayerCapacity G K (z+2))+4*ρ at fold
  rw [joint_layer_capacity_sum] at fold
  have whole := strict_two_interior_inventories G K n m hs ht hn hm pn pm (by omega) cap top d rank strict
  have funding : 4*ρ+2*highestWidth n m r≤D*ρ := by
    have six := Nat.mul_le_mul_right ρ deg
    change highestWidth n m r≤ρ at width;omega
  change (D-1)*(K.roots.ncard+2*matchingEdges (G.induce K.core))+D*ρ+
    (G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+interiorInventory (G.induce K.rest) D+
    interiorInventory (eraseInternal G K.core) D<2*interiorArea n m r D+2*highestWidth n m r+2*d at whole
  omega

#print axioms single_escape_large_top_impossible
end JSP452Audit.StarHost
