import ExactOriginalProfileLossAtEveryHeightOnAnyLaterRow
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_joint_peak_history_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let d := F.rank-matchingEdges F.G
    (∀p,0<originalThresholdCount F.n (p+1) →
      2*(d+∑i,(F.n i-1)/2)+originalThresholdCount F.n (p+1)≤peakCountAbove Y p+1) ∧
    (∀p,0<originalThresholdCount F.m (p+1) →
      2*(d+∑i,(F.m i-1)/2)+originalThresholdCount F.m (p+1)≤peakCountAbove Y p+1) ∧
    ∀j x y,WinsHeight F.n F.m r (j+2) x y →
      widthAt F.n F.m r (j+2)≤peakCountAbove Y j+actualCoordinateLoss P.capacity P.paidCore.ncard r x y := by
  intro Y r d
  obtain ⟨ac,bc,first,second,_,_⟩ := strict_payable_exterior_endpoints F paid P
  obtain ⟨long,_,pos,_,_⟩ := strict_payable_exterior_constraints F paid P
  change P.capacity+r+d+1≤min F.s F.t at long
  obtain ⟨ls,lt⟩ := le_min_iff.mp long
  have pn : 0<F.t-r-P.capacity := by omega
  have pm : 0<F.s-r-P.capacity := by omega
  constructor
  · intro p live
    obtain ⟨sz,lo⟩ := exact_peak_inventory_cut Y p
    have found := endpoint_stage_inventory Y F.hs F.n F.pn first pos pn ac _ lo live
    simpa only [sz] using found
  constructor
  · intro p live
    obtain ⟨sz,lo⟩ := exact_peak_inventory_cut Y p
    have found := endpoint_stage_inventory Y F.ht F.m F.pm second pos pm bc _ lo live
    simpa only [sz] using found
  · intro j x y win
    obtain ⟨sz,lo⟩ := exact_peak_inventory_cut Y j
    have cut := ((strict_exterior_typed_column_inventory F paid P win).2.2 (peakPrefix Y (peakCountAbove Y j))).2
      (by omega) (fun v => Nat.lt_of_le_of_lt (lo v) (by omega))
    rw [sz] at cut
    change widthAt F.n F.m r (j+2)-actualCoordinateLoss P.capacity P.paidCore.ncard r x y≤peakCountAbove Y j at cut
    omega

#print axioms strict_joint_peak_history_inventory
end JSP452Audit.StarHost
