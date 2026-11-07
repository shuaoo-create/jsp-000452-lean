import ChargeTheUnitAxisToTheFullHeadStageOfTheSameDeletionHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem gap_one_original_top_exceeds_capacity_and_full_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let Z := P.capacity
    let b := peakCountAbove Y H
    let W := widthAt F.n F.m r
    D=H+1 → (Z:ℤ)+b+1≤(W D:ℤ)+P.gamma h := by
  intro D H h Y r R Z b W gap
  let i := Z-R
  change P.gamma h≤-3*(P.excess:ℤ) at credit
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨_,_,_,_,zp,room,all⟩ := full_capacity_prefix_data F paid P E hp (show P.gamma h≤0 by omega)
  obtain ⟨Q,big⟩ := actual_large_payable_component F paid P E hp (show P.gamma h≤0 by omega)
  have eq := rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives Q)
  have bound := all (coreComponentEquiv F.G K.barrier P.positives Q)
  have far : R<Z := by dsimp only [R,r,Z];omega
  have fits (Q:↥P.positives) : matchingEdges Q.val.toSimpleGraph≤r+i+1 := (all Q).trans (by change Z≤r+(Z-(r+1))+1;omega)
  obtain ⟨_,mixed⟩ := gap_one_mixed_refund_stock F paid P E kl hp credit gap
  have gamma : P.gamma h≤0 := by omega
  by_cases enough:i≤peakCountAbove Y (H-1)
  · have raw := (strict_peak_history_truncated_profile F paid P i ((Nat.sub_le _ _).trans room) (by omega) fits).2
    change (D:ℤ)*Z+(∑j∈Finset.range D,min i (peakCountAbove Y j):ℕ)+1≤(∑j∈Finset.range D,min (i+Z) (W (j+1)):ℕ)+P.gamma h at raw
    have init : (∑j∈Finset.range H,min i (peakCountAbove Y j))=H*i := by
      calc
        _ = ∑_j∈Finset.range H,i := Finset.sum_congr rfl (fun j hj => min_eq_left
          (enough.trans (peak_counts_antitone Y (by have := Finset.mem_range.mp hj;omega))))
        _ = _ := by simp
    have upper : (∑j∈Finset.range H,min (i+Z) (W (j+1)))≤H*(i+Z) := by
      simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using
        Finset.sum_le_sum (s:=Finset.range H) (fun j _ => Nat.min_le_left (i+Z) (W (j+1)))
    rw [gap,Finset.sum_range_succ,Finset.sum_range_succ,init] at raw
    rw [Nat.mul_add] at upper
    have eqn : (H+1)*Z=H*Z+Z := Nat.succ_mul _ _
    change (Z:ℤ)+b+1≤(W D:ℤ)+P.gamma h
    rw [gap]
    change _+((H*i+min i b:ℕ):ℤ)+1≤(((_+min (i+Z) (W (H+1))):ℕ):ℤ)+P.gamma h at raw
    omega
  · have axis (j:ℕ) (hj:j<H) : W (j+1)≤Z+peakCountAbove Y j := by
      by_cases live:0<W (j+1)
      · obtain ⟨x,y,real⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<j+1) live
        have win : WinsHeight F.n F.m r (j+1) x y := real
        have ht := win.2.2.1
        have left := win.1
        have right := win.2.1
        have unit : x=1 ∨ y=1 := by
          by_contra! both
          have count : j-1+2=j+1 := by omega
          have original : WinsHeight F.n F.m r (j-1+2) x y := count ▸ win
          have stock := (mixed (j-1) x y (by omega) (by omega) original).2
          change i<peakCountAbove Y (H-1) at stock;omega
        exact original_unit_inventory_on_its_own_degree_stage F paid P win unit
      · omega
    have sum := Finset.sum_le_sum (s:=Finset.range H) (fun j hj => axis j (Finset.mem_range.mp hj))
    rw [Finset.sum_add_distrib] at sum
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sum
    have cap (v:↥P.exterior) : Nat.card (Y.neighborSet v)≤D := (induced_neighbor_count_le F.G _ v).trans ((minimal_rank_exact_source F paid).2.2.2.1 v.val)
    have counts := original_full_history_pays_total_inventory Y D cap
    rw [gap,Finset.sum_range_succ] at counts
    have cost := original_physical_truncated_profile F paid P 0
    simp only [Nat.cast_zero,mul_zero,add_zero] at cost
    change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(∑j∈Finset.range D,W (j+1):ℕ)+P.gamma h at cost
    rw [gap,Finset.sum_range_succ] at cost
    have eqn : (H+1)*Z=H*Z+Z := Nat.succ_mul _ _
    rw [gap];dsimp only [b];omega

#print axioms gap_one_original_top_exceeds_capacity_and_full_stage
end JSP452Audit.StarHost