import TheFivePhysicalColumnsForceAHighPlatformFromGapSix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_gap_original_platform_prefix (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let l := P.paidCore.ncard/6
    H+6≤D → P.capacity<widthAt F.n F.m r (H+3) ∧
      6*P.capacity<17*peakCountAbove Y (H+1) ∧ l≤peakCountAbove Y (H+1) ∧
      ∀i≤l,(peakPrefix Y i).ncard=i ∧
        (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+(H+2)*i≤Y.edgeSet.ncard := by
  intro D H r Y l gap
  have large := gap_six_five_columns_cannot_be_low F paid P E hp credit gap
  change P.capacity<widthAt F.n F.m r (H+3) at large
  obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show 0<H+3 by omega) (show 0<widthAt F.n F.m r (H+3) by omega)
  have win : WinsHeight F.n F.m r ((H+1)+2) x y := w
  have a := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1
  have b := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1
  have topX : x≤H := a.trans (Nat.le_max_left _ _)
  have topY : y≤H := b.trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have domain := (strict_double_head_gap_range F paid).2.2.1
  change D-H+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) at domain
  have head : 8≤H := by dsimp only [H] at domain ⊢;omega
  have deg : 14≤D := by omega
  have cap := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 (highestWidth F.n F.m F.r)
  have vol : D*P.positives.ncard≤2*P.capacity := by exact_mod_cast cap.2.2.2.1
  have bound := (Nat.mul_le_mul_right P.positives.ncard deg).trans vol
  have sz := cap.2.2.2.2.2
  have fit : 7*P.paidCore.ncard≤15*P.capacity := by omega
  have tax := (five_column_tax_ratios P.capacity P.paidCore.ncard r x y fit (by omega) (by omega) (by omega)).1
  have inv := (strict_joint_peak_history_inventory F paid P).2.2 (H+1) x y win
  change widthAt F.n F.m r (H+3)≤peakCountAbove Y (H+1)+actualCoordinateLoss P.capacity P.paidCore.ncard r x y at inv
  have many : 6*P.capacity<17*peakCountAbove Y (H+1) := by omega
  have floor : 6*l≤P.paidCore.ncard := Nat.mul_div_le _ _
  have enough : l≤peakCountAbove Y (H+1) := by omega
  refine ⟨large,many,enough,?_⟩
  intro i needed
  have inside := (needed.trans enough).trans (peak_inventory_spec Y (H+1)).1
  refine ⟨(peak_prefix_size Y i).trans (min_eq_left inside),?_⟩
  have price : (H+2)*i≤∑j∈Finset.range i,peakFee Y j := calc
    (H+2)*i=∑_j∈Finset.range i,(H+2) := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => (peak_inventory_spec Y (H+1)).2.2 j |>.1
      ((Finset.mem_range.mp hj).trans_le (needed.trans enough)))
  rw [peak_prefix_edge_account Y i]
  omega

#print axioms six_gap_original_platform_prefix
end JSP452Audit.StarHost
