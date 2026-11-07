import BothMatchingEndpointsAndEveryTypedColumnOnOneActualPeakHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_peak_history_full_profile (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (i:ℕ) (room:i≤P.exterior.ncard) (growth:0<P.cutRoots.ncard+i+P.capacity)
    (small:∀Q:↥P.positives,matchingEdges Q.val.toSimpleGraph≤F.r+P.cutRoots.ncard+i+1) :
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    let U := peakPrefix Y i
    ForcingRow (Y.induce Uᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (r+i+P.capacity) ∧
    (D:ℤ)*P.capacity+(∑j∈Finset.range D,min i (peakCountAbove Y j):ℕ)+1≤
      (∑j∈Finset.range (D+1),min (i+P.capacity) (widthAt F.n F.m r (j+1)):ℕ)+P.gamma h := by
  classical
  intro Y r D h U
  let C := F.G.induce P.paidCore
  let _ := Fintype.ofFinite C.ConnectedComponent
  have size : U.ncard=i := (peak_prefix_size Y i).trans (min_eq_left (by simpa only [Nat.card_coe_set_eq] using room))
  have fits (Q:C.ConnectedComponent) : matchingEdges Q.toSimpleGraph≤r+U.ncard+1 := by
    rw [size]
    exact (rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives Q)).trans_le
      (small (coreComponentEquiv F.G K.barrier P.positives Q))
  have row := actual_payable_exterior_menu F paid P U (split_capacities_of_small _ _ fits)
  rw [size] at row
  refine ⟨row,?_⟩
  have live := F.live
  have smaller : rowCount F.s F.t (r+i+P.capacity)<F.rank := by
    change _<rowCount F.s F.t F.r;dsimp only [r,rowCount] at live ⊢;omega
  have bill := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ row smaller
  have near := (strict_payable_full_profile F paid P).1
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*P.capacity+1≤(rowEnergy F.n F.m r:ℤ)+P.gamma h at near
  have past := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:↥P.exterior) : Nat.card (Y.neighborSet v)≤D := (induced_neighbor_count_le F.G _ v).trans (past v.val)
  have steps := peak_prefix_layer_price Y D i cap
  have top : diagonal F.n F.m (F.r+2)≤D+1 := by dsimp only [D];omega
  have profile := profile_shift_exact_loss F.hs F.ht F.n F.m F.hn F.hm (show F.r≤r by dsimp only [r];omega) top (i+P.capacity)
  rw [←Nat.add_assoc] at profile
  change rowEnergy F.n F.m (r+i+P.capacity)≤(Y.induce Uᶜ).edgeSet.ncard at bill
  change Y.edgeSet.ncard=(Y.induce Uᶜ).edgeSet.ncard+_ at steps
  omega

#print axioms strict_peak_history_full_profile
end JSP452Audit.StarHost
