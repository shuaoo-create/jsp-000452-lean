import EveryPaidExteriorDeletionMustLoseTheSignedRootCredit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_high_actual_core_and_history (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    ∃(K:DegreeRegion F.G D) (k c:ℕ) (P:ScaledPortPlan K k c),0<k ∧ Nonempty (PortGraphLayers P) ∧
      h≤P.excess ∧ 1≤h ∧ 4*P.gamma h+((D:ℤ)+1)*P.excess+2*P.beta≤0 ∧
      (D%2=1 → h+1≤P.excess ∧ 4*P.gamma h+((D:ℤ)+3)*P.excess+((D:ℤ)-5)*h+2*P.beta≤0) ∧
      (∃Q:↥P.positives,F.r+P.cutRoots.ncard+2≤matchingEdges Q.val.toSimpleGraph) ∧
      ∀U:Set ↥P.exterior,(∀Q:↥P.positives,matchingEdges Q.val.toSimpleGraph≤F.r+P.cutRoots.ncard+U.ncard+1) →
        let Y := F.G.induce P.exterior
        ForcingRow (Y.induce Uᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+P.cutRoots.ncard+U.ncard+P.capacity) ∧
        (Y.edgeSet.ncard:ℤ)+1≤((Y.induce Uᶜ).edgeSet.ncard:ℤ)+(D:ℤ)*U.ncard+P.gamma h := by
  classical
  intro D h
  obtain ⟨K,k,c,P,hk,⟨E⟩,hp,big,sharp,odd⟩ := strict_high_payable_original_package F paid
  change 4*P.gamma h+((D:ℤ)+1)*P.excess+2*P.beta≤0 at sharp
  have credit : P.gamma h≤0 := by
    have nonneg : (0:ℤ)≤((D:ℤ)+1)*P.excess := by positivity
    omega
  obtain ⟨L,large⟩ := actual_large_payable_component F paid P E hp credit
  let C := F.G.induce P.paidCore
  let labels := coreComponentEquiv F.G K.barrier P.positives
  have eq (Q:C.ConnectedComponent) : matchingEdges Q.toSimpleGraph=matchingEdges (labels Q).val.toSimpleGraph :=
    rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives Q)
  refine ⟨K,k,c,P,hk,⟨E⟩,big,hp,sharp,odd,⟨labels L,(eq L) ▸ large⟩,?_⟩
  intro U fits
  let _ := Fintype.ofFinite C.ConnectedComponent
  have small (Q:C.ConnectedComponent) : matchingEdges Q.toSimpleGraph≤F.r+P.cutRoots.ncard+U.ncard+1 :=
    (eq Q).trans_le (fits (labels Q))
  have caps := split_capacities_of_small _ _ small
  have w := (P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h).2.2.2.2.1
  change (P.shortfall:ℤ)+(F.G.induce P.cutRoots).edgeSet.ncard+h-P.weight≤0 at credit
  have grow : 0<P.cutRoots.ncard+U.ncard+P.capacity := by omega
  exact ⟨actual_payable_exterior_menu F paid P U caps,exact_menu_deletion_price F paid P U caps grow⟩

#print axioms strict_high_actual_core_and_history
end JSP452Audit.StarHost
