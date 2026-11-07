import EveryOriginalGapFromFourOnMustRetainItsThirdHighestNonpeakColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem single_restoration_on_wide_column {A B:Type*} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    {s t r j x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r)
    (win:WinsHeight n m r j x y) (wide:matchingEdges C<widthAt n m r j)
    (budget:Nat.card B/(x+1)+Nat.card B/(y+1)≤matchingEdges C) (lower:3≤x ∧ 3≤y) :
    ExactTypedWidth Y x y (widthAt n m r j-Nat.card B/4) := by
  obtain ⟨px,py,ht,rf,bg,eq⟩ := win
  let a := min (matchingEdges C) (Nat.card B/(x+1))
  let b := min (matchingEdges C) (Nat.card B/(y+1))
  have la : a≤Nat.card B/(x+1) := Nat.min_le_right _ _
  have lb : b≤Nat.card B/(y+1) := Nat.min_le_right _ _
  have smallX : a≤Nat.card B/4 := la.trans (Nat.div_le_div_left (by omega) (by decide))
  have smallY : b≤Nat.card B/4 := lb.trans (Nat.div_le_div_left (by omega) (by decide))
  by_cases red:a<originalThresholdCount n x
  · have next := palette_retains_typed_rectangle Y C C le_rfl n m hn hm px py (genuine_uniform_pack_cap C x px)
      (by rw [sdiff_self];exact uniform_pack_bot_cap y py) red bg row
    change ExactTypedWidth Y x y (originalThresholdCount n x+originalThresholdCount m y-1-r-a-0) at next
    exact actual_typed_width_down Y next (by omega)
  · have blue : b<originalThresholdCount m y := by omega
    have next := palette_retains_typed_rectangle Y C C le_rfl m n hm hn py px (genuine_uniform_pack_cap C y py)
      (by rw [sdiff_self];exact uniform_pack_bot_cap x px) blue rf (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m y)] at next
    change ExactTypedWidth Y y x (originalThresholdCount n x+originalThresholdCount m y-1-r-b-0) at next
    exact actual_typed_width_down Y (exact_typed_width_swap _ next) (by omega)

theorem four_gap_expensive_prefix (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let r := F.r+P.cutRoots.ncard
    let Y := F.G.induce P.exterior
    let l := P.paidCore.ncard/6
    H+4≤D → l≤peakCountAbove Y (D-4) ∧
      ∀i≤l,(peakPrefix Y i).ncard=i ∧
        (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+(D-3)*i≤Y.edgeSet.ncard := by
  intro D H r Y l gap
  let C := F.G.induce P.paidCore
  let N := P.paidCore.ncard
  let Z := P.capacity
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have large := gap_four_last_three_nonpeak_cannot_be_low F paid P E hp credit gap
  change Z<widthAt F.n F.m r (D-2) at large
  obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show 0<D-2 by omega) (show 0<widthAt F.n F.m r (D-2) by omega)
  have win : WinsHeight F.n F.m r (D-2) x y := w
  have xh : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
  have yh : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have lx : 3≤x := by omega
  have ly : 3≤y := by omega
  have fit := (full_capacity_prefix_data F paid P E hp credit).2.2.2.1
  change 16*N≤35*Z at fit
  have dx : N/(x+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have dy : N/(y+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide)
  have budget : N/(x+1)+N/(y+1)≤Z := by
    rcases (show 5≤x ∨ 5≤y by omega) with red|blue
    · have cap : N/(x+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide)
      omega
    · have cap : N/(y+1)≤N/6 := Nat.div_le_div_left (by omega) (by decide)
      omega
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  have row := (strict_payable_exterior_constraints F paid P).2.2.2.2.2
  have actual := single_restoration_on_wide_column Y C F.n F.m F.hn F.hm row win large (size ▸ budget) ⟨lx,ly⟩
  rw [size] at actual
  obtain ⟨card,lo⟩ := exact_peak_inventory_cut Y (D-4)
  have inv := typed_inventory_on_actual_cut Y win.1 win.2.1 (by omega : x+y-1=(D-3)+1) (by omega)
    actual _ (fun v => Nat.lt_of_le_of_lt (lo v) (by omega))
  rw [card] at inv
  change widthAt F.n F.m r (D-2)-N/4≤peakCountAbove Y (D-4) at inv
  have enough : l≤peakCountAbove Y (D-4) := by change N/6≤_;omega
  refine ⟨enough,?_⟩
  intro i legal
  have room := (legal.trans enough).trans (peak_inventory_spec Y (D-4)).1
  refine ⟨(peak_prefix_size Y i).trans (min_eq_left room),?_⟩
  have charge : (D-3)*i≤∑j∈Finset.range i,peakFee Y j := calc
    (D-3)*i=∑_j∈Finset.range i,(D-3) := by simp [Nat.mul_comm]
    _ ≤ _ := Finset.sum_le_sum (fun j hj => by
      have high := ((peak_inventory_spec Y (D-4)).2.2 j).1 ((Finset.mem_range.mp hj).trans_le (legal.trans enough));omega)
  rw [peak_prefix_edge_account Y i];omega

#print axioms single_restoration_on_wide_column
#print axioms four_gap_expensive_prefix
end JSP452Audit.StarHost
