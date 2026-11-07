import TheCommonGapOneFixedListCostUsesItsOwnActualSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem only_gap_automatic_entry (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let N := P.paidCore.ncard
    let Z := P.capacity
    let Y := F.G.induce P.exterior
    let b := peakCountAbove Y H
    let L := widthAt F.n F.m r D
    R+b<N/3 ∧ N/3-R<peakCountAbove Y (H-1) ∧
      (Z:ℤ)+b+1≤(L:ℤ)+P.gamma (highestWidth F.n F.m F.r) ∧ Z<L := by
  intro D H r R N Z Y b L
  have gap : D=H+1 := strict_original_head_gap_is_one F paid
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  let h := highestWidth F.n F.m F.r
  have head := gap_one_original_top_exceeds_capacity_and_full_stage F paid P E kl hp credit gap
  change (Z:ℤ)+b+1≤(L:ℤ)+P.gamma (highestWidth F.n F.m F.r) at head
  have inv := (gap_one_mixed_refund_stock F paid P E kl hp credit gap).1
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have os := (P.exact_weight_and_root_cost E cap h).2.2.2.2.2
  change N=2*Z+P.positives.ncard at os
  obtain ⟨Q,big⟩ := actual_large_payable_component F paid P E hp (by omega)
  have eq := rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives Q)
  have bound := (full_capacity_prefix_data F paid P E hp (by omega)).2.2.2.2.2.2 (coreComponentEquiv F.G K.barrier P.positives Q)
  have zp : 2≤Z := by dsimp only [Z];omega
  have lp : 0<N/3 := by omega
  have cost := (gap_one_fixed_prefix_price F paid P E kl hp credit (N/3) gap lp (by omega) le_rfl).2.2.2
  change (_:ℤ)+min (N/3-R) b+1≤P.gamma (highestWidth F.n F.m F.r)+2*((N/3-N/3:ℕ):ℤ)+((N/4-N/3:ℕ):ℤ)+((N/5-N/3:ℕ):ℤ)+(N/3-R:ℕ) at cost
  exact ⟨by omega,inv,head,by omega⟩

#print axioms only_gap_automatic_entry
end JSP452Audit.StarHost