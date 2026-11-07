import EveryLegalComponentSplitSurvivesAnyActualExteriorDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem exact_menu_deletion_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    [Fintype (F.G.induce P.paidCore).ConnectedComponent] [DecidableEq (F.G.induce P.paidCore).ConnectedComponent]
    (U:Set ↥P.exterior) (menu:SplitCapacities (fun i:(F.G.induce P.paidCore).ConnectedComponent =>
      matchingEdges i.toSimpleGraph) (F.r+P.cutRoots.ncard+U.ncard)) (progress:0<P.cutRoots.ncard+U.ncard+P.capacity) :
    let Y := F.G.induce P.exterior
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    (Y.edgeSet.ncard:ℤ)+1≤((Y.induce Uᶜ).edgeSet.ncard:ℤ)+(D:ℤ)*U.ncard+P.gamma h := by
  intro Y D h
  let shift := P.cutRoots.ncard+U.ncard+P.capacity
  have next := actual_payable_exterior_menu F paid P U menu
  rw [show F.r+P.cutRoots.ncard+U.ncard+P.capacity=F.r+shift by dsimp [shift];omega] at next
  have live := F.live
  have smaller : rowCount F.s F.t (F.r+shift)<F.rank := by
    change _<rowCount F.s F.t F.r
    dsimp only [rowCount,shift] at live ⊢;omega
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ next smaller
  have fee := P.true_exterior_fee (minimal_rank_exact_source F paid).2.2.2.1 h
  change (F.G.edgeSet.ncard:ℤ)+P.gamma h=(Y.edgeSet.ncard:ℤ)+(D:ℤ)*(P.cutRoots.ncard+P.capacity)+h at fee
  have pref : (rowEnergy F.n F.m F.r:ℤ)≤(rowEnergy F.n F.m (F.r+shift):ℤ)+(D:ℤ)*shift+h := by
    exact_mod_cast prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r shift F.live
  have strict : (F.G.edgeSet.ncard:ℤ)+1≤rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
  have bound : (rowEnergy F.n F.m (F.r+shift):ℤ)≤(Y.induce Uᶜ).edgeSet.ncard := by exact_mod_cast pay
  dsimp only [shift] at pref
  push_cast at pref
  linarith only [fee,pref,strict,bound]

theorem actual_large_payable_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    ∃Q:(F.G.induce P.paidCore).ConnectedComponent,F.r+P.cutRoots.ncard+2≤matchingEdges Q.toSimpleGraph := by
  classical
  let C := F.G.induce P.paidCore
  let _ := Fintype.ofFinite C.ConnectedComponent
  by_contra! tiny
  have small (Q:C.ConnectedComponent) : matchingEdges Q.toSimpleGraph≤F.r+P.cutRoots.ncard+1 := by
    have bound := tiny Q;omega
  have row := (strict_payable_exterior_constraints F paid P).2.2.2.2.2
  have shifted := sum_row_whole_component_menu _ C _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) row (split_capacities_of_small _ _ small)
  exact payable_exterior_refuses_full_shift F paid P E hp credit shifted

#print axioms exact_menu_deletion_price
#print axioms actual_large_payable_component
end JSP452Audit.StarHost
