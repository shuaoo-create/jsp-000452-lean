import ThreeNonpeakColumnsPayTheFullUnchangedListMenu
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_four_last_three_nonpeak_cannot_be_low (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    H+4≤D → P.capacity<widthAt F.n F.m r (D-2) := by
  intro D H r gap
  by_contra! low
  let Y := F.G.induce P.exterior
  let Z := P.capacity
  let N := P.paidCore.ncard
  let z := P.positives.ncard
  let L (j:ℕ) := widthAt F.n F.m r (j+2)
  let C (j:ℕ) := peakCountAbove Y j
  obtain ⟨order,few,fit,fitH,pos,room,small⟩ := full_capacity_prefix_data F paid P E hp credit
  change N=2*Z+z at order
  have legal (Q:↥P.positives) : matchingEdges Q.val.toSimpleGraph≤F.r+P.cutRoots.ncard+Z+1 := (small Q).trans (by dsimp [Z];omega)
  obtain ⟨_,need⟩ := strict_peak_history_truncated_profile F paid P Z room (by dsimp [Z];omega) legal
  have inv := (strict_joint_peak_history_inventory F paid P).2.2
  have win (j:ℕ) (live:0<L j) : ∃x y,WinsHeight F.n F.m r (j+2) x y :=
    original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega) live
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have pack := (P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 (highestWidth F.n F.m F.r)).2.2.2.1
  have volume : D*z≤2*Z := by exact_mod_cast pack
  have cnt := (Nat.mul_le_mul_right z deg).trans volume
  have density : 11*N≤24*Z := by omega
  have each (j:ℕ) (_:j<D-1) :
      64*min (2*Z) (L j)≤64*min Z (C j)+64*Z+(if j=1 then 32*z else 0) := by
    by_cases live:0<L j
    · obtain ⟨x,y,w⟩ := win j live
      have inventory := inv j x y w
      change L j≤C j+actualCoordinateLoss Z N r x y at inventory
      have estimate := actual_tax_when_mixed Z N z r x y order fit w.1 w.2.1
      have ht := w.2.2.1
      have same : x+y=4 ↔ j=1 := by omega
      simp only [same] at estimate
      have pay : 8*actualCoordinateLoss Z N r x y≤8*Z+(if j=1 then 4*z else 0) := estimate
      split_ifs at pay ⊢ <;> omega
    · omega
  have last (j:ℕ) (_:j<D-1) (late:D-4≤j) :
      64*min (2*Z) (L j)≤64*min Z (C j)+46*Z ∧ (D-3≤j → 64*min (2*Z) (L j)≤64*min Z (C j)+40*Z) ∧
      (D-2≤j → 64*min (2*Z) (L j)≤64*min Z (C j)+36*Z) := by
    have high : D-2≤j+2 := by omega
    have mono : L j≤widthAt F.n F.m r (D-2) := Finset.card_le_card (fun i hi =>
      Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hi).1,high.trans (Finset.mem_filter.mp hi).2⟩)
    by_cases live:0<L j
    · obtain ⟨x,y,w⟩ := win j live
      have xt := (original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 w.2.2.2.1
      have yt := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 w.2.2.2.2.1
      have a : x≤H := xt.trans (Nat.le_max_left _ _)
      have b : y≤H := yt.trans (Nat.le_max_right _ _)
      have ht := w.2.2.1
      obtain ⟨first,second,third⟩ := three_nonpeak_taxes Z N r x y density (by omega) (by omega) (by omega)
      have inventory := inv j x y w
      change L j≤C j+actualCoordinateLoss Z N r x y at inventory
      change widthAt F.n F.m r (D-2)≤Z at low
      omega
    · omega
  have total := three_nonpeak_area D Z z deg (by omega) _ _ each last
  change 2*Z+(∑j∈Finset.range (D-1),min (2*Z) (L j))≤D*Z+∑j∈Finset.range D,min Z (C j) at total
  change (D:ℤ)*Z+(∑j∈Finset.range D,min Z (C j):ℕ)+1≤
    (∑j∈Finset.range D,min (Z+Z) (widthAt F.n F.m r (j+1)):ℕ)+_ at need
  have split := Finset.sum_range_succ' (fun j => min (Z+Z) (widthAt F.n F.m r (j+1))) (D-1)
  rw [show D-1+1=D by omega] at split
  rw [split,←two_mul Z] at need
  change (D:ℤ)*Z+(∑j∈Finset.range D,min Z (C j):ℕ)+1≤
    ((∑j∈Finset.range (D-1),min (2*Z) (L j))+min (2*Z) (widthAt F.n F.m r 1):ℕ)+P.gamma (highestWidth F.n F.m F.r) at need
  omega

#print axioms gap_four_last_three_nonpeak_cannot_be_low
end JSP452Audit.StarHost
