import ThePenultimateColumnPaysEveryShortOrMiddleFixedStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem gap_two_forces_a_long_high_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let G := P.gamma h
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let Z := P.capacity
    let N := P.paidCore.ncard
    let u := peakCountAbove Y H
    D=H+2 → 4*G+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 → N/3<R+u := by
  intro D H h G Y r R Z N u gap sharp
  let z := P.positives.ncard
  let ρ := P.excess
  let b := peakCountAbove Y (H+1)
  let L := widthAt F.n F.m r (H+1)
  let e := minimumExposure (F.G.induce P.paidCore) D
  let l := max (N/4) (R+u)
  let i := l-R
  let X := Y.induce (peakPrefix Y i)ᶜ
  let C := F.G.induce P.paidCore
  let n := fixedCoreList C F.n l
  let m := fixedCoreList C F.m l
  let g := (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)
  let p := H/2
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have rp : 0<R := by dsimp only [R];omega
  have posρ : 0<ρ := by dsimp only [ρ];omega
  have cut := P.positive_count_with_original_roots E
  have roots : z+1≤R+ρ := by dsimp only [z,R,r,ρ];omega
  have linear := gap_two_linear_degree_credit D h ρ G deg hp hρ (by linarith only [sharp,show (0:ℤ)≤P.beta by positivity])
  have credit : G≤-3*(ρ:ℤ) := by omega
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  have edges := P.exact_weight_and_root_cost E cap h
  have os := edges.2.2.2.2.2
  change N=2*Z+z at os
  have cost := edges.2.2.2.1
  change (D:ℤ)*z≤2*Z at cost
  have room : 11*z≤2*Z := by exact_mod_cast (mul_le_mul_of_nonneg_right (show (11:ℤ)≤D by omega) (show (0:ℤ)≤z by positivity)).trans cost
  obtain ⟨_,_,endStage⟩ := gap_two_excludes_both_high_alternatives F paid P E kl hp hρ gap sharp
  have startPrice := gap_two_last_two_prices F paid P E kl hp credit gap
  have big := startPrice.2.2.2.2.1
  change Z<L at big
  have lower := startPrice.2.2.2.2.2.2.2 endStage
  change (_:ℤ)+2*Z+b+1≤(L:ℤ)+(N:ℤ)/4+e+G at lower
  have floor : (2:ℤ)*Z+b+1≤(L:ℤ)+(N/4:ℕ)+e+G := by omega
  have holes := (gap_two_top_typed F paid P E kl gap).1
  by_contra! short
  have pos : 0<l := by dsimp only [l];omega
  have lo : N/5≤l := by dsimp only [l];omega
  have hi : l≤N/3 := by dsimp only [l];omega
  have mid : N/4≤l := le_max_left _ _
  have iu : u ≤ i := by dsimp only [i,l];omega
  have order : b≤u := peak_counts_antitone Y (by omega)
  obtain ⟨live,smaller,row,bill⟩ := gap_two_fixed_prefix_price F paid P E kl hp credit l gap pos lo hi
  change ForcingRow X _ _ (padDemand n) (padDemand m) (r+i+l) at row
  have hs := F.hs
  have ht := F.ht
  have sp : 0<min F.s ((componentBudget C F.n).len+l) := by omega
  have tp : 0<min F.t ((componentBudget C F.m).len+l) := by omega
  have hn := protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l
  have hm := protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l
  have pn := protected_demand_positive F.n _ F.pn ((componentBudget C F.n).entries_positive _ F.pn) l
  have pm := protected_demand_positive F.m _ F.pm ((componentBudget C F.m).entries_positive _ F.pm) l
  have baseline := paid sp tp n m hn hm pn pm _ _ row smaller
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at baseline
  have nonneg : 0≤g := by dsimp only [g];omega
  have fee : g+Z+l+u+b+1≤G+2*((N/3:ℕ):ℤ)+2*i := by
    change ((X.edgeSet.ncard-rowEnergy n m (r+i+l):ℕ):ℤ)+Z+l+min i u+min i b+1≤
      G+2*((N/3:ℕ):ℤ)+2*((N/4-l:ℕ):ℤ)+2*i at bill
    dsimp only [g];omega
  have limit := (peak_fee_antitone Y iu).trans (peak_inventory_spec Y H).2.1
  have capX (v) : Nat.card (X.neighborSet v)≤H := ((chosenPeakStep Y (peakPrefix Y i)).cap v).trans limit
  have ceiling := live_row_height_at_degree_cap X sp tp n m hn hm pn pm row live capX
  have sel := smaller_row_exposure_budget sp tp n m hn hm pn pm X (r+i+l) H F.rank (by omega) row live smaller paid capX ceiling
  change ((H:ℤ)-2)*minimumExposure X H≤2*(p:ℤ)*(p+1)+2*g at sel
  obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<H+1) (by omega : 0<L)
  have wins : WinsHeight F.n F.m r (H+1) x y := win
  have hx : x≤H := ((original_threshold_prefix F.n F.hn x ⟨0,F.hs⟩).2 wins.2.2.2.1).trans (Nat.le_max_left _ _)
  have hy : y≤H := ((original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 wins.2.2.2.2.1).trans (Nat.le_max_right _ _)
  have ht' := wins.2.2.1
  obtain ⟨actual,_,wprice⟩ := fixed_winner_typed_after_prefix X C F.n F.m F.hn F.hm l i pos wins row
  let w := originalThresholdCount n x+originalThresholdCount m y-1-(r+i+l)
  change ExactTypedWidth X x y w at actual
  rw [Nat.card_coe_set_eq] at wprice
  change L≤w+i+l+fixedHeadLoss Z N l x+fixedHeadLoss Z N l y at wprice
  have slot (v:ℕ) : (2≤v → fixedHeadLoss Z N l v≤N/3-l) ∧ (3≤v → fixedHeadLoss Z N l v=0) := by
    unfold fixedHeadLoss
    exact ⟨fun hv => by have h : N/(v+1)≤N/3 := Nat.div_le_div_left (by omega) (by decide);omega,
      fun hv => by have h : N/(v+1)≤N/4 := Nat.div_le_div_left (by omega) (by decide);omega⟩
  obtain ⟨a,aa⟩ := slot x
  obtain ⟨c,cc⟩ := slot y
  have width : L≤w+i+N/3 := by omega
  have actualE := typed_width_exposure_at_cap X H x y w (by omega) capX wins.1 wins.2.1 ht' actual
  obtain ⟨wide,upper⟩ := gap_two_short_middle_cost D Z N z ρ R b u l i L w e G g deg os room roots rp posρ holes linear rfl short rfl floor width nonneg fee
  have same : (D-2)/2=p := by dsimp only [p];omega
  rw [same] at wide upper
  have delta := mul_nonneg (show (0:ℤ)≤(H:ℤ)-8 by omega) (show (0:ℤ)≤(w:ℤ)-p-3 by omega)
  exact gap_two_selector_separation H p w _ g (by omega) rfl nonneg (by linarith only [upper,delta]) wide actualE sel

#print axioms gap_two_forces_a_long_high_stage
end JSP452Audit.StarHost