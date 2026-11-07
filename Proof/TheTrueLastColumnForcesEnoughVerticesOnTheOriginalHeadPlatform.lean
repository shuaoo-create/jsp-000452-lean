import AtGapTwoTheLastNonpeakColumnHasOnlyActualInternalHoles
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_initial_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let d := F.rank-matchingEdges F.G
    let R := F.r+P.cutRoots.ncard+1
    let i := P.capacity-R
    D=H+2 → R<P.capacity ∧ i<2*d ∧ i<peakCountAbove (F.G.induce P.exterior) (H-1) := by
  intro D H d R i gap
  let N := P.paidCore.ncard
  let Z := P.capacity
  let r := F.r+P.cutRoots.ncard
  let Y := F.G.induce P.exterior
  let L (j:ℕ) := widthAt F.n F.m r (j+2)-uniformEnvelope Y (j+2)
  let e := minimumExposure (F.G.induce P.paidCore) D
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 9≤H := by omega
  obtain ⟨sz,_,fit,_,_,_,caps⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  obtain ⟨Q,large⟩ := actual_large_payable_component F paid P E hp (by omega)
  have same := rank_eq_of_graph_iso (coreComponentIso F.G K.barrier P.positives Q)
  have bound := caps (coreComponentEquiv F.G K.barrier P.positives Q)
  have largeZ : R<Z := by dsimp only [R,Z];omega
  obtain ⟨holes,_,_,top,_⟩ := gap_two_top_typed F paid P E kl gap
  change e≤P.excess at holes
  change widthAt F.n F.m r D≤uniformEnvelope Y D+N/4+e at top
  rw [gap] at top
  have root := P.positive_count_with_original_roots E
  have per (j:ℕ) : 2*L j≤2*Z+(if j=1 then P.excess else 0) := by
    by_cases active:0<widthAt F.n F.m r (j+2)
    · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<j+2) active
      have win : WinsHeight F.n F.m r (j+2) x y := w
      have inv := (strict_exterior_typed_column_inventory F paid P win).2.1
      change widthAt F.n F.m r (j+2)-actualCoordinateLoss Z N r x y≤uniformEnvelope Y (j+2) at inv
      have bound := true_third_gap_taxes Z N P.positives.ncard P.excess r x y fit sz (by dsimp only [r];omega) win.1 win.2.1
      have ht := win.2.2.1
      simp only [show x+y=4 ↔ j=1 by omega] at bound
      dsimp only [L];omega
    · have zero : L j=0 := by dsimp only [L];omega
      simp [zero]
  have sum := Finset.sum_le_sum (s:=Finset.range H) (fun j _ => per j)
  have exc : (∑j∈Finset.range H,if j=1 then P.excess else 0)=P.excess := by simp [show 1<H by omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,exc,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sum
  let loss := ∑j∈Finset.range (D-1),L j
  have vol := original_exterior_deficit_volume F paid P D rfl L (by intro j _;dsimp only [L,r,Y];omega)
  change (D:ℤ)*Z+1≤(Z:ℤ)+d+loss+P.gamma (highestWidth F.n F.m F.r) at vol
  have mult : D*Z=H*Z+2*Z := by rw [gap,Nat.add_mul]
  have split : loss=(∑j∈Finset.range H,L j)+L H := by dsimp only [loss];rw [show D-1=H+1 by omega,Finset.sum_range_succ]
  have finalLoss : L H≤N/4+e := by dsimp only [L];omega
  change N=2*Z+P.positives.ncard at sz
  have rootLimit : P.positives.ncard≤R+P.excess := by dsimp only [R];omega
  have small : i<2*d := by change Z-R<2*d;omega
  refine ⟨largeZ,small,?_⟩
  have stages := strict_joint_peak_history_inventory F paid P
  have hh : H-1+1=H := by omega
  rcases le_total (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) with red|blue
  · have eq : H=F.m ⟨0,F.ht⟩ := max_eq_right red
    have yes : 0<originalThresholdCount F.m (H-1+1) := (original_threshold_prefix F.m F.hm _ ⟨0,F.ht⟩).1 (by rw [hh,eq])
    have r := stages.2.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    change i<peakCountAbove Y (H-1);omega
  · have eq : H=F.n ⟨0,F.hs⟩ := max_eq_left blue
    have yes : 0<originalThresholdCount F.n (H-1+1) := (original_threshold_prefix F.n F.hn _ ⟨0,F.hs⟩).1 (by rw [hh,eq])
    have r := stages.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    change i<peakCountAbove Y (H-1);omega


#print axioms gap_two_initial_inventory
end JSP452Audit.StarHost