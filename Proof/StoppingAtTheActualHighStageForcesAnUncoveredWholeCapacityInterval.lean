import EveryGapTwoRootMustFinishAtTheOriginalHeadAndHasNoExtraWidth
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem finishing_one_full_stage_forces_extra_width (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let Z := P.capacity
    let u := peakCountAbove Y (D-2)
    let b := peakCountAbove Y (D-1)
    let X := Y.induce (peakPrefix Y u)ᶜ
    0<Z → ForcingRow X F.s F.t (padDemand F.n) (padDemand F.m) (r+u+Z) →
      (Z:ℤ)+b+1≤(widthAt F.n F.m r D:ℤ)+P.gamma h := by
  intro D h Y r Z u b X zp row
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have live := F.live
  have less : rowCount F.s F.t (r+u+Z)<F.rank := by
    change _<rowCount F.s F.t F.r;dsimp only [r,rowCount] at live ⊢;omega
  have price := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ row less
  change rowEnergy F.n F.m (r+u+Z)≤X.edgeSet.ncard at price
  let area (v:ℕ) := ∑j∈Finset.range D,widthAt F.n F.m v (j+1)
  let T := D-1
  have last : T+1=D := by dsimp only [T];omega
  have cost := original_physical_truncated_profile F paid P 0
  simp only [Nat.cast_zero,mul_zero,add_zero] at cost
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(area r:ℤ)+P.gamma h at cost
  have loss : area r≤area (r+u+Z)+T*(u+Z)+widthAt F.n F.m r D := by
    have each (j:ℕ) : widthAt F.n F.m r (j+1)≤widthAt F.n F.m (r+u+Z) (j+1)+(u+Z) := by
      rw [Nat.add_assoc r u Z,widthAt_shift F.hs F.ht F.n F.m F.hn F.hm r (u+Z) (j+1)];omega
    have sum := Finset.sum_le_sum (s:=Finset.range T) (fun j _ => each j)
    rw [Finset.sum_add_distrib] at sum
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sum
    dsimp only [area]
    conv_lhs => rw [←last,Finset.sum_range_succ,last]
    conv_rhs => enter [1,1];rw [←last,Finset.sum_range_succ]
    omega
  have part : area (r+u+Z)≤rowEnergy F.n F.m (r+u+Z) := partial_profile_area_le F.hs F.ht F.n F.m F.hn F.hm _ _
  have cap (v:↥P.exterior) : Nat.card (Y.neighborSet v)≤D :=
    (induced_neighbor_count_le F.G _ v).trans ((minimal_rank_exact_source F paid).2.2.2.1 v.val)
  have steps := peak_prefix_layer_price Y D u cap
  change Y.edgeSet.ncard=X.edgeSet.ncard+_ at steps
  have init : (∑j∈Finset.range T,min u (peakCountAbove Y j))=T*u := by
    calc
      _ = ∑_j∈Finset.range T,u := Finset.sum_congr rfl (fun j hj => min_eq_left
        (peak_counts_antitone Y (by have := Finset.mem_range.mp hj;dsimp only [T] at this;omega)))
      _ = _ := by simp
  rw [←last,Finset.sum_range_succ,init] at steps
  have order : b≤u := peak_counts_antitone Y (by omega)
  change Y.edgeSet.ncard=X.edgeSet.ncard+(T*u+min u b) at steps
  rw [min_eq_right order] at steps
  have spent : (Y.edgeSet.ncard:ℤ)=(X.edgeSet.ncard:ℤ)+((T:ℤ)*u+b) := by exact_mod_cast steps
  have profile : (area r:ℤ)≤(X.edgeSet.ncard:ℤ)+(T:ℤ)*(u+Z)+(widthAt F.n F.m r D:ℤ) := by
    exact_mod_cast loss.trans (Nat.add_le_add_right (Nat.add_le_add_right (part.trans price) _) _)
  have degree : (D:ℤ)=T+1 := by exact_mod_cast last.symm
  rw [degree] at cost
  linarith only [cost,profile,spent]

theorem gap_two_whole_capacity_menu_fails (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    [Fintype (F.G.induce P.paidCore).ConnectedComponent] [DecidableEq (F.G.induce P.paidCore).ConnectedComponent]
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let u := peakCountAbove Y H
    D=H+2 → 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 →
      ¬SplitCapacities (fun Q:(F.G.induce P.paidCore).ConnectedComponent => matchingEdges Q.toSimpleGraph) (r+u) := by
  intro D H h r Y u gap sharp menu
  obtain ⟨_,upper,short⟩ := gap_two_excludes_both_high_alternatives F paid P E kl hp hρ gap sharp
  change u < P.capacity-(r+1) at short
  let U := peakPrefix Y u
  have sz : U.ncard=u := (peak_prefix_size Y u).trans (min_eq_left (peak_inventory_spec Y H).1)
  have row := actual_payable_exterior_menu F paid P U (by rw [sz];exact menu)
  rw [sz] at row
  have strong := finishing_one_full_stage_forces_extra_width F paid P
  change 0<P.capacity → ForcingRow (Y.induce (peakPrefix Y (peakCountAbove Y (D-2)))ᶜ) F.s F.t
    (padDemand F.n) (padDemand F.m) (r+peakCountAbove Y (D-2)+P.capacity) →
    (P.capacity:ℤ)+peakCountAbove Y (D-1)+1≤(widthAt F.n F.m r D:ℤ)+P.gamma h at strong
  rw [show D-2=H by omega,show D-1=H+1 by omega] at strong
  have impossible := strong (by omega) row
  change (widthAt F.n F.m r D:ℤ)+P.gamma h≤(P.capacity:ℤ)+peakCountAbove Y (H+1) at upper
  omega

#print axioms finishing_one_full_stage_forces_extra_width
#print axioms gap_two_whole_capacity_menu_fails
end JSP452Audit.StarHost