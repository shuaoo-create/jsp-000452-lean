import TwoDirectCostComparisonsExcludeTheHighThreeHeadAndExtraWidthCases
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem gap_two_excludes_both_high_alternatives (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
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
    let L := widthAt F.n F.m r D
    let u := peakCountAbove Y H
    let b := peakCountAbove Y (H+1)
    D=H+2 → 4*G+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 →
      (Z<L → ∀x y,WinsHeight F.n F.m r D x y → 4≤min x y) ∧
      (L:ℤ)+G≤(Z:ℤ)+b ∧ u < Z-R := by
  intro D H h G Y r R Z L u b gap sharp
  let N := P.paidCore.ncard
  let z := P.positives.ncard
  let ρ := P.excess
  let l := max (N/5) (R+b)
  let i := l-R
  let p := (H+1)/2
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 9≤H := by omega
  have rp : 0<R := by dsimp only [R];omega
  have posρ : 0<ρ := by dsimp only [ρ];omega
  have gain := mul_nonneg (show (0:ℤ)≤(D:ℤ)-11 by omega) (show (0:ℤ)≤ρ by positivity)
  have pos := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤h by positivity)
  change 4*G+((D:ℤ)+2)*ρ+((D:ℤ)-6)*h+2*P.beta≤0 at sharp
  have linear : 4*G+13*ρ≤0 := by linarith only [sharp,gain,pos,show (0:ℤ)≤P.beta by positivity]
  have credit : G≤-3*(ρ:ℤ) := by omega
  have edges := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have os := edges.2.2.2.2.2
  change N=2*Z+z at os
  have cost := edges.2.2.2.1
  change (D:ℤ)*z≤2*Z at cost
  have small : 11*z≤2*Z := by
    have le := mul_le_mul_of_nonneg_right (show (11:ℤ)≤D by omega) (show (0:ℤ)≤z by positivity)
    exact_mod_cast le.trans cost
  have roots : z+1≤R+ρ := by have := P.positive_count_with_original_roots E;dsimp only [z,R,r,ρ];omega
  have peak := (gap_two_initial_inventory F paid P E kl hp credit gap).1
  change R<Z at peak
  have reduced : 4*G+((H:ℤ)+4)*ρ+((H:ℤ)-4)*h≤0 := by rw [gap] at sharp;push_cast at sharp;linarith only [sharp,show (0:ℤ)≤P.beta by positivity]
  have single (hi:Z<L) (x y:ℕ) (win:WinsHeight F.n F.m r D x y) :
      4≤min x y ∧ (L:ℤ)+G≤(Z:ℤ)+b := by
    let S := Y.induce (peakPrefix Y i)ᶜ
    let C := F.G.induce P.paidCore
    let g := (S.edgeSet.ncard:ℤ)-rowEnergy (fixedCoreList C F.n l) (fixedCoreList C F.m l) (r+i+l)
    let e := minimumExposure S (H+1)
    obtain ⟨nonneg,bill,sel,wins⟩ := gap_two_high_fixed_selector F paid P E kl hp credit gap hi
    change 0≤g at nonneg
    change g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) at bill
    change ((H:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g at sel
    obtain ⟨w,_,expo,narrow,wide,three⟩ := wins x y win
    change L≤w+i+N/4 at narrow
    have shape := ((gap_two_top_typed F paid P E kl gap).2.2.1 x y win).1
    have four : 4≤min x y := by
      by_contra! tiny
      have fee := gap_two_three_head_cost_ceiling Z N z ρ R b l i L w G g os small roots rp linear rfl rfl hi narrow bill
      exact gap_two_three_head_selector_false H p w e g head rfl nonneg fee (three (by omega)) sel
    refine ⟨four,?_⟩
    by_contra! more
    have fee := gap_two_four_head_cost_ceiling Z N z ρ R b l i L w G g os small roots rp (by omega) posρ rfl rfl (by omega) (wide four) bill
    exact gap_two_four_head_selector_false H p w e h ρ G g head rfl hp hρ reduced nonneg fee expo sel
  have upper : (L:ℤ)+G≤(Z:ℤ)+b := by
    by_cases hi:Z<L
    · obtain ⟨x,y,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) (by omega : 0<L)
      exact (single hi x y w).2
    · omega
  refine ⟨fun hi x y win => (single hi x y win).1,upper,?_⟩
  by_contra! enough
  have other := (gap_two_last_two_prices F paid P E kl hp credit gap).2.2.2.2.2.2.1 enough
  change (_:ℤ)+Z+b+1≤(widthAt F.n F.m r (H+2):ℤ)+G at other
  have same : L=widthAt F.n F.m r (H+2) := congrArg (widthAt F.n F.m r) gap
  omega

#print axioms gap_two_excludes_both_high_alternatives
end JSP452Audit.StarHost