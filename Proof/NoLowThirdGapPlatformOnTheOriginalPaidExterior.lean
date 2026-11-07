import ExactLowPlatformComparisonOnTheThirdGapHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_gap_low_impossible (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (kl:0<k) (hp:0<highestWidth F.n F.m F.r)
    (credit:P.gamma (highestWidth F.n F.m F.r)≤ -2*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D=H+3 → P.capacity<widthAt F.n F.m (F.r+P.cutRoots.ncard) (D-1) := by
  intro D H gap
  by_contra! low
  let Y := F.G.induce P.exterior
  let Z := P.capacity
  let N := P.paidCore.ncard
  let r := F.r+P.cutRoots.ncard
  let h := highestWidth F.n F.m F.r
  let W (j:ℕ) := widthAt F.n F.m r j
  let C (j:ℕ) := peakCountAbove Y j
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨order,_,_,fit,pos,room,small⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  change N=2*Z+P.positives.ncard at order
  change 16*N≤35*Z at fit
  have rks := (P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h).2.2.2.1
  have rank : D*P.positives.ncard≤2*Z := by exact_mod_cast rks
  have cnt := (Nat.mul_le_mul_right P.positives.ncard deg).trans rank
  have ample := (third_gap_initial_inventory F paid P E hp (by omega) gap).2
  change Z<C (H-1) at ample
  have full (j:ℕ) (hj:j<H) : Z≤C j := ample.le.trans (peak_counts_antitone Y (by omega))
  obtain ⟨top,prior⟩ := third_gap_top_two_inventories F paid P E kl gap
  change W D≤C (D-2)+N/5+P.excess at top
  have a : D-1=H+2 := by omega
  have b : D-2=H+1 := by omega
  have e : D-3=H := by omega
  rw [b,gap] at top
  have roots := P.positive_count_with_original_roots E
  have debt : ((W (H+2)-C H:ℕ):ℤ)+(W (H+3)-C (H+1):ℕ)+P.gamma h≤Z := by
    change P.gamma h≤ -2*(P.excess:ℤ) at credit
    by_cases active:0<W (D-1)
    · obtain ⟨x,y,z⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
        (show 0<D-1 by omega) active
      have win : WinsHeight F.n F.m r (D-1) x y := z
      obtain ⟨when,three⟩ := prior x y win
      by_cases just:min x y=3
      · have near := when just
        change W (D-1)≤C (D-3)+N/4+P.excess at near
        rw [a,e] at near;omega
      · have ht := win.2.2.1
        have J := four_head_root_corrected_point Z N P.positives.ncard P.excess r x y order cnt
          (by dsimp only [r];omega) (by omega) (by omega) (by omega)
        have w : WinsHeight F.n F.m r (H+2) x y := a ▸ win
        have inv := (strict_joint_peak_history_inventory F paid P).2.2 H x y w
        change W (H+2)≤C H+actualCoordinateLoss Z N r x y at inv
        omega
    · rw [a] at active;omega
  change W (D-1)≤Z at low
  rw [a] at low
  have low' : W (H+3)≤Z := (Finset.card_le_card (fun j hj =>
    Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,(show H+2≤H+3 by omega).trans (Finset.mem_filter.mp hj).2⟩) :
    W (H+3)≤W (H+2)) |>.trans low
  have total := third_low_history_sum H Z W C (P.gamma h) full low low' debt
  have legal (Q:↥P.positives) : matchingEdges Q.val.toSimpleGraph≤F.r+P.cutRoots.ncard+Z+1 :=
    (small Q).trans (by dsimp only [Z];omega)
  obtain ⟨_,need⟩ := strict_peak_history_truncated_profile F paid P Z room (by dsimp only [Z];omega) legal
  let spent := ∑j∈Finset.range (H+3),min Z (C j)
  let area := ∑j∈Finset.range (H+3),min (2*Z) (W (j+1))
  change (D:ℤ)*Z+(∑j∈Finset.range D,min Z (C j):ℕ)+1≤(∑j∈Finset.range D,min (Z+Z) (W (j+1)):ℕ)+P.gamma h at need
  rw [gap,←two_mul Z] at need
  change (area:ℤ)+P.gamma h≤((H+3)*Z+spent:ℕ) at total
  change ((H+3:ℕ):ℤ)*Z+spent+1≤(area:ℤ)+P.gamma h at need
  omega

#print axioms third_gap_low_impossible
end JSP452Audit.StarHost
