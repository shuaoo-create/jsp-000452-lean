import EvenTwoCoreMassIsAlreadyIncompatibleWithTheActualHighSelector
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_requires_an_actual_singleton_package (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    D=H+2 → 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 → P.excess=1 := by
  intro D H h gap sharp
  let G := P.gamma h
  let Y := F.G.induce P.exterior
  let C := F.G.induce P.paidCore
  let r := F.r+P.cutRoots.ncard
  let R := r+1
  let N := P.paidCore.ncard
  let Z := P.capacity
  let L := widthAt F.n F.m r D
  let b := peakCountAbove Y (H+1)
  let l := max (N/5) (R+b)
  let i := l-R
  let p := H/2
  let X := Y.induce (peakPrefix Y i)ᶜ
  let e := minimumExposure X (H+1)
  let g := (X.edgeSet.ncard:ℤ)-rowEnergy (fixedCoreList C F.n l) (fixedCoreList C F.m l) (r+i+l)
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have rp : 0<R := by dsimp only [R];omega
  have posρ : 0<P.excess := by omega
  have cap := (minimal_rank_exact_source F paid).2.2.2.1
  by_contra! no
  by_cases low:L≤Z
  · exact no (gap_two_low_platform_requires_singleton F paid P E kl hp hρ gap sharp low)
  have high : Z<L := by omega
  have few := gap_two_high_platform_has_at_most_two_cores F paid P E kl hp hρ gap sharp high
  obtain ⟨count,odd⟩ := P.excess_has_distinct_positive_support E (by omega : 0<D) posρ cap
  have two : P.positives.ncard=2 := by omega
  have pair : P.excess=2 := by omega
  have even : D%2=0 := by omega
  have doubles : H=2*p := by dsimp only [p];omega
  have dp : D=2*p+2 := by omega
  have sz := (P.exact_weight_and_root_cost E cap h).2.2.2.2.2
  change N=2*Z+P.positives.ncard at sz
  rw [two] at sz
  have long := gap_two_forces_a_long_high_stage F paid P E kl hp hρ gap sharp
  have mass := (gap_two_long_stage_has_a_dominant_real_core F paid P E kl hp hρ gap sharp long).2.1
  change 6*((D+1)/2)*(P.positives.ncard-1)+P.positives.ncard<Z at mass
  rw [two] at mass
  have credit := gap_two_linear_degree_credit D h P.excess G deg hp hρ (by linarith only [sharp,show (0:ℤ)≤P.beta by positivity])
  have small : G≤-3*(P.excess:ℤ) := by omega
  have lower := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤(h:ℤ)-1 by omega)
  change 4*G+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 at sharp
  have debt : 2*G+3*p+2≤0 := by
    have twoZ : (P.excess:ℤ)=2 := by exact_mod_cast pair
    rw [twoZ] at sharp
    linarith only [lower,sharp,show (D:ℤ)=2*p+2 by exact_mod_cast dp,show (0:ℤ)≤P.beta by positivity]
  obtain ⟨nonneg,bill,price,targets⟩ := gap_two_high_fixed_selector F paid P E kl hp small gap high
  change 0≤g at nonneg
  change g+Z+2*l+R+b+1≤G+2*((N/3:ℕ):ℤ)+2*((N/4:ℕ):ℤ) at bill
  change ((H:ℤ)-1)*e≤2*(((H+1)/2:ℕ):ℤ)*((((H+1)/2:ℕ):ℤ)+1)+2*g at price
  rw [show (H+1)/2=p by omega] at price
  obtain ⟨x,y,win⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (by omega : 0<D) (by omega : 0<L)
  obtain ⟨w,_,we,_,wide,_⟩ := targets x y win
  have keep := wide ((gap_two_excludes_both_high_alternatives F paid P E kl hp hρ gap (by change 4*G+_+_+_≤0;exact sharp)).1 high x y win)
  change L≤w+i+l at keep
  have mode : l=max ((2*Z+2)/5) (R+b) := by dsimp only [l];rw [sz]
  rw [sz] at bill
  apply gap_two_even_two_core_price_false p Z R b l i L w e G g (by omega) rp (by omega) debt mode rfl high keep nonneg we bill
  rw [show (H:ℤ)=2*p by exact_mod_cast doubles] at price;exact price

theorem strict_gap_two_has_one_original_odd_regular_component (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D=H+2 → D%2=0 ∧ highestWidth F.n F.m F.r=1 ∧ (oddRegularComponents F.G D).ncard=1 := by
  intro D H gap
  obtain ⟨K,k,c,P,kl,⟨E⟩,hp,hρ,sharp,_,one⟩ := strict_original_credit_and_singleton F paid
  obtain ⟨parity,height,reg,_⟩ := one (gap_two_requires_an_actual_singleton_package F paid P E kl hp hρ gap sharp)
  exact ⟨parity,height,reg⟩

#print axioms gap_two_requires_an_actual_singleton_package
#print axioms strict_gap_two_has_one_original_odd_regular_component
end JSP452Audit.StarHost