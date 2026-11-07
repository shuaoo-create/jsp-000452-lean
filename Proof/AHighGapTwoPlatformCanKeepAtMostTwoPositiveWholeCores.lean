import EveryGapTwoRootMustContinuePastTheOneThirdStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_high_platform_has_at_most_two_cores (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let G := P.gamma h
    let r := F.r+P.cutRoots.ncard
    let R := r+1
    let Z := P.capacity
    let L := widthAt F.n F.m r D
    D=H+2 → 4*G+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 → Z<L → P.positives.ncard≤2 := by
  intro D H h G r R Z L gap sharp hi
  let Y := F.G.induce P.exterior
  let b := peakCountAbove Y (H+1)
  let N := P.paidCore.ncard
  let z := P.positives.ncard
  let ρ := P.excess
  let l := max (N/5) (R+b)
  let i := l-R
  let p := (H+1)/2
  let S := Y.induce (peakPrefix Y i)ᶜ
  let C := F.G.induce P.paidCore
  let g := (S.edgeSet.ncard:ℤ)-rowEnergy (fixedCoreList C F.n l) (fixedCoreList C F.m l) (r+i+l)
  let e := minimumExposure S (H+1)
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 9≤H := by omega
  have rp : 0<R := by dsimp only [R];omega
  have posρ : 0<ρ := by dsimp only [ρ];omega
  have linear := gap_two_linear_degree_credit D h ρ G deg hp hρ (by linarith only [sharp,show (0:ℤ)≤P.beta by positivity])
  have credit : G≤-3*(ρ:ℤ) := by omega
  have os := (P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h).2.2.2.2.2
  change N=2*Z+z at os
  have roots : z+1≤R+ρ := by have := P.positive_count_with_original_roots E;dsimp only [z,R,r,ρ];omega
  have long := gap_two_forces_a_long_high_stage F paid P E kl hp hρ gap sharp
  have mass := (gap_two_long_stage_has_a_dominant_real_core F paid P E kl hp hρ gap sharp long).2.1
  change 6*((D+1)/2)*(z-1)+z<Z at mass
  obtain ⟨nonneg,bill,sel,wins⟩ := gap_two_high_fixed_selector F paid P E kl hp credit gap hi
  change 0≤g at nonneg
  change g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) at bill
  change ((H:ℤ)-1)*e≤2*(p:ℤ)*(p+1)+2*g at sel
  obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) (by omega : 0<L)
  obtain ⟨w,_,we,_,wide,_⟩ := wins x y win
  have four := (gap_two_excludes_both_high_alternatives F paid P E kl hp hρ gap sharp).1 hi x y win
  have bound := wide four
  change L≤w+i+l at bound
  by_contra! many
  obtain ⟨size,cost⟩ := gap_two_dominant_mass_cost D Z N z ρ R b l i L w G g deg many posρ os roots rp mass linear rfl rfl hi bound nonneg bill
  have same : (D-1)/2=p := by dsimp only [p];omega
  rw [same] at size cost
  have delta := mul_nonneg (show (0:ℤ)≤(H:ℤ)-9 by omega) (show (0:ℤ)≤(w:ℤ)-p-3 by omega)
  have tag : ((H:ℤ)+1-2)*e≤2*(p:ℤ)*(p+1)+2*g := by linarith only [sel]
  apply gap_two_selector_separation (H+1) p w e g (by omega) rfl nonneg _ size we
  · push_cast;exact tag
  · push_cast;linarith only [cost,delta]

#print axioms gap_two_high_platform_has_at_most_two_cores
end JSP452Audit.StarHost