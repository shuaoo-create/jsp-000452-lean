import ADeadPairLosesTheWholeRootAllowanceOnTheSameOriginalColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem gap_two_low_platform_requires_singleton (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let G := P.gamma h
    let r := F.r+P.cutRoots.ncard
    D=H+2 → 4*G+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 →
      widthAt F.n F.m r D≤P.capacity → P.excess=1 := by
  intro D H h G r gap sharp low
  let ρ := P.excess
  let Z := P.capacity
  let N := P.paidCore.ncard
  let C := F.G.induce P.paidCore
  let Y := F.G.induce P.exterior
  let R := r+1
  let i := Z-R
  let U := peakPrefix Y i
  let X := Y.induce Uᶜ
  let g := (X.edgeSet.ncard:ℤ)-rowEnergy F.n F.m (r+i+Z)
  let L := widthAt F.n F.m r (H+1)
  let u := peakCountAbove Y H
  let b := peakCountAbove Y (H+1)
  let p := H/2
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have posρ : 0<ρ := by dsimp only [ρ];omega
  by_contra! no
  have large : 2≤ρ := by change ρ≠1 at no;omega
  have linear := gap_two_linear_degree_credit D h ρ G deg hp hρ (by linarith only [sharp,show (0:ℤ)≤P.beta by positivity])
  have credit : G≤-3*(ρ:ℤ) := by omega
  have long := gap_two_forces_a_long_high_stage F paid P E kl hp hρ gap sharp
  change N/3<R+u at long
  have short := (gap_two_excludes_both_high_alternatives F paid P E kl hp hρ gap sharp).2.2
  change u < i at short
  have ib := (gap_two_initial_inventory F paid P E kl hp credit gap).1
  change R<Z at ib
  obtain ⟨row,live,smaller,bill,big,_,_,_⟩ := gap_two_last_two_prices F paid P E kl hp credit gap
  change ForcingRow X _ _ (padDemand F.n) (padDemand F.m) (r+i+Z) at row
  change Z<L at big
  have paidX := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ row smaller
  change rowEnergy F.n F.m (r+i+Z)≤X.edgeSet.ncard at paidX
  have nonneg : 0≤g := by dsimp only [g];omega
  have bu : b≤u := peak_counts_antitone Y (by omega)
  have cost : g+Z+u+b+1≤(L:ℤ)+G := by
    change ((X.edgeSet.ncard-rowEnergy F.n F.m (r+i+Z):ℕ):ℤ)+2*Z+min i u+min i b+1≤
      (min (i+Z) L:ℕ)+(min (i+Z) (widthAt F.n F.m r (H+2)):ℕ)+G at bill
    have same : widthAt F.n F.m r (H+2)=widthAt F.n F.m r D := congrArg _ gap.symm
    change widthAt F.n F.m r D≤Z at low
    dsimp only [g];omega
  obtain ⟨x,y,wins⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<H+1) (by omega : 0<L)
  have win : WinsHeight F.n F.m r (H+1) x y := wins
  have hx : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 win.2.2.2.1).trans (Nat.le_max_left _ _)
  have hy : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 win.2.2.2.2.1).trans (Nat.le_max_right _ _)
  have ht := win.2.2.1
  have ratio := (full_capacity_prefix_data F paid P E hp (show G≤0 by omega)).2.2.2.1
  change 16*N≤35*Z at ratio
  have slot (v:ℕ) (hv:2≤v) : N/(v+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide)
  have alive := positive_monochrome_or_two_root_bounded_counts Y C F.n F.m F.hn F.hm
    (strict_payable_exterior_constraints F paid P).2.2.2.2.2 win (show 0<L by omega)
  rw [Nat.card_coe_set_eq] at alive
  change ExactTypedWidth Y x y (L-N/(min x y+1)) ∨ L+R≤N/(x+1)+N/(y+1) at alive
  have typed : ExactTypedWidth Y x y (L-N/3) := by
    rcases alive with yes|dead
    · exact actual_typed_width_down _ yes (by have := slot (min x y) (by omega);omega)
    · have a := slot x (by omega)
      have b := slot y (by omega)
      omega
  let w := L-N/3-i
  have cap := (peak_fee_antitone Y short.le).trans (peak_inventory_spec Y H).2.1
  have capX (v) : Nat.card (X.neighborSet v)≤H := ((chosenPeakStep Y U).cap v).trans cap
  have avail := (full_capacity_prefix_data F paid P E hp (show G≤0 by omega)).2.2.2.2.2.1
  change Z≤P.exterior.ncard at avail
  have sz : U.ncard=i := (peak_prefix_size Y i).trans (min_eq_left (by rw [Nat.card_coe_set_eq];dsimp only [i];omega))
  have seen := typed_width_after_deletion Y U win.1 win.2.1 typed
  rw [sz] at seen
  have tax := typed_width_exposure_at_cap X H x y w (by omega) capX win.1 win.2.1 ht seen
  have limit := live_row_height_at_degree_cap X F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row live capX
  have sel := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm X (r+i+Z) H F.rank (by omega) row live smaller paid capX limit
  change ((H:ℤ)-2)*minimumExposure X H≤2*(p:ℤ)*(p+1)+2*g at sel
  have eq : i+R=Z := Nat.sub_add_cancel ib.le
  have cheap : g≤(w:ℤ)-p-3 := by dsimp only [w,p];omega
  have wide : p+3≤w := by omega
  have delta := mul_nonneg (show (0:ℤ)≤(H:ℤ)-4 by omega) (show (0:ℤ)≤(w:ℤ)-p-3 by omega)
  exact gap_two_selector_separation H p w _ g (by omega) rfl nonneg (by linarith only [delta,cheap]) wide tax sel

#print axioms gap_two_low_platform_requires_singleton
end JSP452Audit.StarHost