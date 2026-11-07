import SixActualUpperColumnsExcludeEveryLargeGapLowPlatform
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem high_gap_original_platform_prefix (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let l := P.paidCore.ncard/7
    H+8≤D → P.capacity<widthAt F.n F.m r (H+4) ∧
      3*P.capacity<8*peakCountAbove Y (H+2) ∧ l≤peakCountAbove Y (H+2) ∧
      ∀i≤l,(peakPrefix Y i).ncard=i ∧
        (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+(H+3)*i≤Y.edgeSet.ncard := by
  intro D H r Y l gap
  have large := high_gap_six_columns_cannot_be_low F paid P E hp credit gap
  change P.capacity<widthAt F.n F.m r (H+4) at large
  obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show 0<H+4 by omega) (show 0<widthAt F.n F.m r (H+4) by omega)
  have win : WinsHeight F.n F.m r ((H+2)+2) x y := w
  have a := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1
  have b := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1
  have topX : x≤H := a.trans (Nat.le_max_left _ _)
  have topY : y≤H := b.trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have fit := (full_capacity_prefix_data F paid P E hp credit).2.2.2.1
  have tax := actual_tax_when_both_large P.capacity P.paidCore.ncard r x y fit (by omega) (by omega)
  have inv := (strict_joint_peak_history_inventory F paid P).2.2 (H+2) x y win
  change widthAt F.n F.m r (H+4)≤peakCountAbove Y (H+2)+actualCoordinateLoss P.capacity P.paidCore.ncard r x y at inv
  have many : 3*P.capacity<8*peakCountAbove Y (H+2) := by omega
  have floor : 7*l≤P.paidCore.ncard := Nat.mul_div_le _ _
  have enough : l≤peakCountAbove Y (H+2) := by omega
  refine ⟨large,many,enough,?_⟩
  intro i needed
  have inside := (needed.trans enough).trans (peak_inventory_spec Y (H+2)).1
  refine ⟨(peak_prefix_size Y i).trans (min_eq_left inside),?_⟩
  have price : (H+3)*i≤∑j∈Finset.range i,peakFee Y j := calc
    (H+3)*i=∑_j∈Finset.range i,(H+3) := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => (peak_inventory_spec Y (H+2)).2.2 j |>.1
      ((Finset.mem_range.mp hj).trans_le (needed.trans enough)))
  rw [peak_prefix_edge_account Y i]
  omega

#print axioms high_gap_original_platform_prefix
end JSP452Audit.StarHost
