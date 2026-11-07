import TheOriginalMatchingDeficitPaysEveryNonpeakEnvelopeLoss
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_gap_initial_inventory (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let d := F.rank-matchingEdges F.G
    D=H+3 → P.capacity<2*d ∧ P.capacity<peakCountAbove (F.G.induce P.exterior) (H-1) := by
  intro D H d gap
  let N := P.paidCore.ncard
  let Z := P.capacity
  let r := F.r+P.cutRoots.ncard
  let Y := F.G.induce P.exterior
  let L (j:ℕ) := widthAt F.n F.m r (j+2)-uniformEnvelope Y (j+2)
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 8≤H := by omega
  obtain ⟨sz,_,fit,_,_,_,_⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  have root := P.positive_count_with_original_roots E
  have per (j:ℕ) : 2*L j≤2*Z+(if j=1 then P.excess else 0) ∧
      (H≤j → 3*L j≤N) := by
    by_cases active:0<widthAt F.n F.m r (j+2)
    · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<j+2) active
      have win : WinsHeight F.n F.m r (j+2) x y := w
      have inv := (strict_exterior_typed_column_inventory F paid P win).2.1
      change widthAt F.n F.m r (j+2)-actualCoordinateLoss Z N r x y≤uniformEnvelope Y (j+2) at inv
      have tax : L j≤actualCoordinateLoss Z N r x y := by dsimp only [L];omega
      have bound := true_third_gap_taxes Z N P.positives.ncard P.excess r x y fit sz (by dsimp only [r];omega) win.1 win.2.1
      have ht := win.2.2.1
      simp only [show x+y=4 ↔ j=1 by omega] at bound
      refine ⟨by omega,?_⟩
      intro high
      have xh : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
      have yh : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
      by_cases x3:x=3
      · have v := bounded_point_tax_ratio Z N r x y 3 8 (by decide) (by decide) (by omega) (by omega)
        change 35*actualCoordinateLoss Z N r x y≤11*N at v;omega
      by_cases y3:y=3
      · have v := bounded_point_tax_ratio Z N r x y 8 3 (by decide) (by decide) (by omega) (by omega)
        change 35*actualCoordinateLoss Z N r x y≤11*N at v;omega
      have v := bounded_point_tax_ratio Z N r x y 4 4 (by decide) (by decide) (by omega) (by omega)
      change 24*actualCoordinateLoss Z N r x y≤8*N at v;omega
    · have zero : L j=0 := by dsimp only [L];omega
      simp [zero]
  have sum := Finset.sum_le_sum (s:=Finset.range H) (fun j _ => (per j).1)
  have exc : (∑j∈Finset.range H,if j=1 then P.excess else 0)=P.excess := by simp [show 1<H by omega]
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,exc,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at sum
  have high1 := (per H).2 le_rfl
  have high2 := (per (H+1)).2 (by omega)
  let loss := ∑j∈Finset.range (D-1),L j
  have combined : 6*loss≤6*(H*Z)+3*P.excess+4*N := by
    dsimp only [loss];rw [show D-1=H+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ]
    omega
  have vol := original_exterior_deficit_volume F paid P D rfl L (by intro j _;dsimp only [L,r,Y];omega)
  change (D:ℤ)*Z+1≤(Z:ℤ)+d+loss+P.gamma (highestWidth F.n F.m F.r) at vol
  have mult : D*Z=H*Z+3*Z := by rw [gap,Nat.add_mul]
  have first : Z<2*d := by change 5*N≤11*Z at fit;omega
  refine ⟨first,?_⟩
  have stages := strict_joint_peak_history_inventory F paid P
  have hh : H-1+1=H := by omega
  rcases le_total (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) with red|blue
  · have eq : H=F.m ⟨0,F.ht⟩ := max_eq_right red
    have yes : 0<originalThresholdCount F.m (H-1+1) := (original_threshold_prefix F.m F.hm _ ⟨0,F.ht⟩).1 (by rw [hh,eq])
    have r := stages.2.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    change Z<peakCountAbove Y (H-1);omega
  · have eq : H=F.n ⟨0,F.hs⟩ := max_eq_left blue
    have yes : 0<originalThresholdCount F.n (H-1+1) := (original_threshold_prefix F.n F.hn _ ⟨0,F.hs⟩).1 (by rw [hh,eq])
    have r := stages.1 (H-1) yes
    change 2*(d+_)+_≤peakCountAbove Y (H-1)+1 at r
    change Z<peakCountAbove Y (H-1);omega

#print axioms third_gap_initial_inventory
end JSP452Audit.StarHost
