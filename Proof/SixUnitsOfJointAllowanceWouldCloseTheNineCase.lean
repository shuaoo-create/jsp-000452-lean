import ThreeKindsOfUnpaidColumnsInTheActualNineSource
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_actual_residual_columns_below_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s)
    (j : ℕ) (positive : 0<j) : R.basicPrice F.n F.m F.r j≤R.jointPrice j := by
  let W := componentBudget (F.G.induce R.chosen) F.n
  let J := commonErasedDemand F.n W R.roots.ncard R.totalCapacity
  have live : 0<W.len := (nine_long_side_actual_source_prices F paid nine R long).1
  have rows := (strict_nine_two_physical_rows F paid nine R).1
  have first := widthAt_le_uniformEnvelope live F.ht (W.entries F.n) F.m (W.entries_antitone F.n F.hn) F.hm
    (W.entries_positive F.n F.pn) F.pm _ _ j rows.1 positive
  have last := widthAt_le_uniformEnvelope live F.ht J F.m
    (common_erased_antitone F.n F.hn W R.roots.ncard R.totalCapacity) F.hm
    (common_erased_positive F.n W R.roots.ncard R.totalCapacity) F.pm _ _ j rows.2 positive
  change widthAt (W.entries F.n) F.m (F.r+R.roots.ncard) j≤uniformEnvelope (F.G.induce R.outside) j at first
  change widthAt J F.m F.r j≤uniformEnvelope R.retainedEdges j at last
  change R.roots.ncard+2*R.totalCapacity+widthAt (W.entries F.n) F.m (F.r+R.roots.ncard) j+
    widthAt J F.m F.r j≤R.roots.ncard+2*R.totalCapacity+uniformEnvelope (F.G.induce R.outside) j+uniformEnvelope R.retainedEdges j
  omega

theorem strict_nine_joint_allowance_six_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (funded : 2*interiorArea F.n F.m F.r 9+2*(F.rank-matchingEdges F.G-R.rankAllowance)≤
      (∑j∈Finset.range 8,R.jointPrice (j+2))+6) : False := by
  have account := strict_nine_joint_matching_inventory F paid nine R
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have debt := (R.root_deleted_edge_account cap).2
  have allowance := (R.root_deleted_rank_allowance cap).1
  have roots := R.root_count.2
  have h := (strict_nine_original_peak F paid nine).2.1
  change R.roots.ncard≤2 at roots
  omega

theorem strict_nine_aligned_short_source_exists (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) :
    ∃R : NinePortRegion F.G,(highestWidth F.n F.m F.r:ℤ)≤R.K.eta ∧
      ((F.s+5≤R.totalCapacity ∧ R.totalCapacity+F.r+10≤F.t) ∨
        (F.t+5≤R.totalCapacity ∧ R.totalCapacity+F.r+10≤F.s)) := by
  obtain ⟨R,width,_⟩ := strict_nine_port_region_exists F paid nine
  exact ⟨R,width,strict_nine_exactly_one_short_list F paid nine R⟩

#print axioms nine_actual_residual_columns_below_inventory
#print axioms strict_nine_joint_allowance_six_impossible
#print axioms strict_nine_aligned_short_source_exists
end JSP452Audit.StarHost
