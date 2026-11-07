import TheThreeClippedColumnsMustPayForTheSingleRegularBlock
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem regular_lowest_stage_platform (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let W := widthAt F.n F.m F.r
    let O := B.outside
    let N := Nat.card B.piece.supp
    let i := B.P-(F.r+1)
    let U := peakPrefix O i
    let Y := O.induce Uᶜ
    let g := Y.edgeSet.ncard-rowEnergy F.n F.m (F.r+i+B.P)
    peakCountAbove O H ≤ i → W (H+1)≤B.P ∨ W (H+1)≤g+(p-1)+N/3+i := by
  intro H W O N i U Y g after
  change H+3=2*p at head
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  obtain ⟨_,_,sz,live,smaller,row,bill⟩ := regular_block_inventory_and_next F paid B degree head one
  change U.ncard=i at sz
  by_cases tiny:W (H+1)≤B.P
  · exact Or.inl tiny
  right
  have liveW : 0<W (H+1) := by omega
  obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (show 0<H+1 by omega) liveW
  have real : WinsHeight F.n F.m F.r (H+1) x y := win
  have lower := (regular_third_gap_block_widths F paid p B degree head one).2.2.2 x y
    (by rw [show 2*p-2=H+1 by omega];exact real)
  rw [show 2*p-2=H+1 by omega] at lower
  change _ ∧ (ExactTypedWidth O x y (W (H+1)-N/3) ∨ W (H+1)≤B.P) at lower
  have typed := lower.2.resolve_right tiny
  have actual := typed_width_after_deletion O U real.1 real.2.1 typed
  rw [sz] at actual
  have cap (v:↥(Uᶜ:Set ↥(B.piece.suppᶜ:Set F.X))) : Nat.card (Y.neighborSet v)≤H :=
    ((chosenPeakStep O U).cap v).trans ((peak_fee_antitone O after).trans (peak_inventory_spec O H).2.1)
  have cost := typed_width_exposure_at_cap Y H x y (W (H+1)-N/3-i) (by omega) cap real.1 real.2.1 real.2.2.1 actual
  have height := live_row_height_at_degree_cap Y F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row live cap
  have price := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+i+B.P) H F.rank
    (by omega) row live smaller paid cap height
  change rowEnergy F.n F.m (F.r+i+B.P)≤Y.edgeSet.ncard at bill
  have gain : (Y.edgeSet.ncard:ℤ)-rowEnergy F.n F.m (F.r+i+B.P)=g := by dsimp only [g];omega
  rw [gain,show H/2=p-2 by omega] at price
  push_cast [Nat.cast_sub (by omega : 2≤p)] at price
  let rho := minimumExposure Y H
  have charge : rho≤g+(p-1) := by
    by_contra! high
    have cash := mul_nonneg (show (0:ℤ)≤(H:ℤ)-2 by omega) (show (0:ℤ)≤(rho:ℤ)-g-p by omega)
    have nonneg := mul_nonneg (show (0:ℤ)≤(H:ℤ)-4 by omega) (show (0:ℤ)≤g by positivity)
    have hx : (H:ℤ)=2*p-3 := by omega
    change ((H:ℤ)-2)*rho≤_ at price
    rw [hx] at price cash nonneg
    linarith only [price,cash,nonneg,show (6:ℤ)≤p by exact_mod_cast many]
  change W (H+1)-N/3-i≤rho at cost
  omega

#print axioms regular_lowest_stage_platform
end JSP452Audit.StarHost
