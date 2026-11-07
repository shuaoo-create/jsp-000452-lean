import TheThirdGapHasMoreThanItsWholeCapacityInRealHeadDegreeVertices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_gap_high_platform (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let N := P.paidCore.ncard
    let Y := F.G.induce P.exterior
    let L := widthAt F.n F.m r (D-1)
    D=H+3 → P.capacity<L → ∃x y,WinsHeight F.n F.m r (D-1) x y ∧
      ((x=3 ∧ y=H) ∨ (y=3 ∧ x=H) ∨ (4≤x ∧ 4≤y)) ∧
      ExactTypedWidth Y x y (L-N/4) ∧ N/5≤peakCountAbove Y (D-3) ∧
      ∀i≤N/5,(peakPrefix Y i).ncard=i ∧ (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+(D-2)*i≤Y.edgeSet.ncard := by
  intro D H r N Y L gap high
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show 0<D-1 by omega) (show 0<widthAt F.n F.m r (D-1) by omega)
  have win : WinsHeight F.n F.m r (D-1) x y := w
  have a : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
  have b : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have x3 : 3≤x := by omega
  have y3 : 3≤y := by omega
  have ratio := (full_capacity_prefix_data F paid P E hp credit).2.2.2.1
  change 16*N≤35*P.capacity at ratio
  have X : N/(x+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have B : N/(y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have budget : N/(x+1)+N/(y+1)≤P.capacity := by
    rcases (show 5≤x ∨ 5≤y by omega) with first|second
    · have smaller : N/(x+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide)
      omega
    · have smaller : N/(y+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide)
      omega
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  have row := (strict_payable_exterior_constraints F paid P).2.2.2.2.2
  have actual := single_restoration_on_wide_column Y _ F.n F.m F.hn F.hm row win high (size ▸ budget) ⟨x3,y3⟩
  rw [size] at actual
  obtain ⟨sz,lo⟩ := exact_peak_inventory_cut Y (D-3)
  have inv := typed_inventory_on_actual_cut Y win.1 win.2.1 (by omega : x+y-1=(D-2)+1) (by omega)
    actual _ (fun v => Nat.lt_of_le_of_lt (lo v) (by omega))
  rw [sz] at inv
  change L-N/4≤peakCountAbove Y (D-3) at inv
  have enough : N/5≤peakCountAbove Y (D-3) := by omega
  refine ⟨x,y,win,by omega,actual,enough,?_⟩
  intro i take
  have room := (take.trans enough).trans (peak_inventory_spec Y (D-3)).1
  have charge : (D-2)*i≤∑j∈Finset.range i,peakFee Y j := calc
    (D-2)*i=∑_j∈Finset.range i,(D-2) := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => by
      have before := ((Finset.mem_range.mp hj).trans_le (take.trans enough))
      have expensive := ((peak_inventory_spec Y (D-3)).2.2 j).1 before;omega)
  refine ⟨(peak_prefix_size Y i).trans (min_eq_left room),?_⟩
  rw [peak_prefix_edge_account Y i];omega

#print axioms third_gap_high_platform
end JSP452Audit.StarHost
