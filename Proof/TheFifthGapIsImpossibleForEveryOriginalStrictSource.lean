import TheExactSignedPriceLeftByEveryFourOrFiveGapPackage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_original_head_gap_at_most_four (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D-H≤4 := by
  intro D H
  have above := strict_original_head_gap_at_most_five F paid
  change D-H≤5 at above
  by_contra! large
  have headGap : D=H+5 := by omega
  have range := (strict_double_head_gap_range F paid).2.2.1
  change D-H+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) at range
  have head : 7≤H := by dsimp only [H] at range ⊢;omega
  obtain ⟨K,k,c,P,_,⟨E⟩,hp,_,signed,_⟩ := strict_high_payable_original_package F paid
  let h := highestWidth F.n F.m F.r
  have credit : P.gamma h≤0 := by
    change 4*P.gamma h+((D:ℤ)+1)*P.excess+2*P.beta≤0 at signed
    have nonneg : (0:ℤ)≤((D:ℤ)+1)*P.excess := by positivity
    omega
  let Z := P.capacity
  let N := P.paidCore.ncard
  let l := N/6
  let i := l-(F.r+P.cutRoots.ncard+1)
  have cap := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have rank : D*P.positives.ncard≤2*Z := by exact_mod_cast cap.2.2.2.1
  have lim := (Nat.mul_le_mul_right P.positives.ncard (show 12≤D by omega)).trans rank
  have order := cap.2.2.2.2.2
  change N=2*Z+P.positives.ncard at order
  have budget : 2*threeSmallCaps N+l≤4*Z := by dsimp only [threeSmallCaps,l];omega
  obtain ⟨_,bill,fee⟩ := strict_four_five_signed_price F paid P E hp credit (by change H+4≤D;omega) head
  change _+((D:ℤ)-H-1)*Z+4*l+1≤P.gamma h+2*threeSmallCaps N+((D:ℤ)-H-3)*l+3*i at fee
  rw [show (D:ℤ)-H-1=4 by omega,show (D:ℤ)-H-3=2 by omega] at fee
  have few : i≤l := Nat.sub_le _ _
  omega

#print axioms strict_original_head_gap_at_most_four
end JSP452Audit.StarHost
