import DoubleSubcapTopSurplus
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- A surviving nonunit in the joined residual contradicts strictness
whenever the top is a large mixed winner. No candidate palette is
charged on a different graph. -/
theorem subcap_nonunit_residual_impossible {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (deg : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r)
    (width : highestWidth n m r≤minimumExposure G D)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (space : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (mass : (∑j,m j)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (esc : matchingEdges (G.induce K.core)<s) (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y) :
    originalThresholdCount (commonErasedDemand n (componentBudget (G.induce K.core) n)
      K.roots.ncard (matchingEdges (G.induce K.core))) 2=0 := by
  by_contra! nonzero
  have nonunit : 0<originalThresholdCount (commonErasedDemand n (componentBudget (G.induce K.core) n)
    K.roots.ncard (matchingEdges (G.induce K.core))) 2 := by omega
  have higher := mixed_top_surplus G K n m r d pm deg endpoint space mass reserve winner
  have lower := nonunit_J_covers_lower_layers G K n m r (rowCount s t r) d hs ht hn hm pn pm esc kinds data nonunit
  have axes := sum_actual_matching_axes G K n m ht hn hm pn pm row (by omega)
  have all : (∑q∈Finset.range (D-1),axisAllowance G K n m r (q+2))≤2*∑i,(n i-1)/2 := by
    rw [axis_allowance_sum _ _ _ _ _ (by omega)];exact axes
  have fold := fold_top_layer_payment D d (∑i,(n i-1)/2) (widthAt n m r) (jointLayerCapacity G K)
    (axisAllowance G K n m r) (by omega) higher (fun j lo _ => lower j lo) all
  rw [joint_layer_capacity_sum] at fold
  change 2*interiorArea n m r D+2*d≤_ at fold
  have deficit := strict_two_interior_inventories G K n m hs ht hn hm pn pm (by omega) cap top d rank strict
  have cushion : 2*highestWidth n m r≤D*minimumExposure G D :=
    (Nat.mul_le_mul_left 2 width).trans (Nat.mul_le_mul_right _ (by omega))
  omega

#print axioms subcap_nonunit_residual_impossible
end JSP452Audit.StarHost
