import AThreeHeadWinnerCannotPayTheSameWholeCoreExposure
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem last_gap_excludes_every_three_head_winner (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (hρ:highestWidth F.n F.m F.r≤P.excess) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ))
    {x y:ℕ} (win:WinsHeight F.n F.m (F.r+P.cutRoots.ncard) (diagonal F.n F.m (F.r+2)-1) x y) : min x y≠3 := by
  intro three
  let D := diagonal F.n F.m (F.r+2)-1
  let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
  let h := highestWidth F.n F.m F.r
  let G := P.gamma h
  let C := F.G.induce P.paidCore
  let Y := F.G.induce P.exterior
  let r := F.r+P.cutRoots.ncard
  let R := r+1
  let Z := P.capacity
  let N := P.paidCore.ncard
  let ρ := P.excess
  let z := P.positives.ncard
  let b := peakCountAbove Y H
  let L := widthAt F.n F.m r D
  let l := max (N/5) (R+b)
  let i := l-R
  let p := H/2
  let X := Y.induce (peakPrefix Y i)ᶜ
  let e := minimumExposure X H
  let g := (X.edgeSet.ncard:ℤ)-rowEnergy (fixedCoreList C F.n l) (fixedCoreList C F.m l) (r+i+l)
  let w := L-N/4-i
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have gap : D=H+1 := strict_original_head_gap_is_one F paid
  have rp : 0<R := by dsimp only [R];omega
  have posρ : 0<ρ := by dsimp only [ρ];omega
  have edges := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have os := edges.2.2.2.2.2
  change N=2*Z+z at os
  have demand := edges.2.2.2.1
  change (D:ℤ)*z≤2*Z at demand
  have room : 11*z≤2*Z := by exact_mod_cast (mul_le_mul_of_nonneg_right (show (11:ℤ)≤D by omega) (show (0:ℤ)≤z by positivity)).trans demand
  have roots : z+1≤R+ρ := by have := P.positive_count_with_original_roots E;dsimp only [z,R,r,ρ];omega
  obtain ⟨short,_,wide,_⟩ := only_gap_automatic_entry F paid P E kl hp credit
  change R+b<N/3 at short
  change (Z:ℤ)+b+1≤(L:ℤ)+G at wide
  have hi : l≤N/3 := by dsimp only [l];omega
  obtain ⟨nonneg,cost,price,_,wins⟩ := last_gap_smaller_row_and_exposure F paid P E kl hp credit l
    (le_max_right _ _) (by change N/6≤l;dsimp only [l];omega) hi
  obtain ⟨_,_,fee⟩ := wins x y win
  rw [three] at fee
  change 3=3 → (D-2)*w≤2*e at fee
  change 0≤g at nonneg
  change g+b+1≤G+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ)+i at cost
  change ((H:ℤ)-2)*e≤2*(p:ℤ)*(p+1)+2*g at price
  have ceiling := one_gap_three_head_cost Z N z ρ R b l i L w G g os room roots rp posρ credit rfl rfl hi wide (by dsimp only [w];omega) cost
  apply one_gap_three_head_selector_false (D-2) p w e g (by omega) (by dsimp only [p];omega) nonneg ceiling (fee rfl)
  rw [show ((D-2:ℕ):ℤ)=(H:ℤ)-1 by omega]
  linarith only [price]

#print axioms last_gap_excludes_every_three_head_winner
end JSP452Audit.StarHost