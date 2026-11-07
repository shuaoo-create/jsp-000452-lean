import CompareTheSingleProtectedRowWithEveryOriginalColumn
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_original_head_gap_at_most_seven (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D-H≤7 := by
  intro D H
  by_contra! large
  have gap : H+8≤D := by omega
  have terms := strict_double_head_gap_range F paid
  change 1≤D-H ∧ _ ∧ D-H+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) ∧ _ at terms
  have head : 10≤H := by dsimp only [H];omega
  have low : 18≤D := by omega
  obtain ⟨K,k,c,P,_,⟨E⟩,hp,_,sharp,_⟩ := strict_high_payable_original_package F paid
  let h := highestWidth F.n F.m F.r
  have credit : P.gamma h≤0 := by
    change 4*P.gamma h+((D:ℤ)+1)*P.excess+2*P.beta≤0 at sharp
    have nonneg : (0:ℤ)≤((D:ℤ)+1)*P.excess := by positivity
    omega
  let C := F.G.induce P.paidCore
  let Y := F.G.induce P.exterior
  let Z := P.capacity
  let N := P.paidCore.ncard
  let r := F.r+P.cutRoots.ncard
  let l := N/7
  let i := l-(r+1)
  let X := Y.induce (peakPrefix Y i)ᶜ
  let n := fixedCoreList C F.n l
  let m := fixedCoreList C F.m l
  have a := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have sz := a.2.2.2.2.2
  change N=2*Z+P.positives.ncard at sz
  have count : D*P.positives.ncard≤2*Z := by exact_mod_cast a.2.2.2.1
  have cost := (Nat.mul_le_mul_right P.positives.ncard low).trans count
  have ratio : 9*N≤19*Z := by omega
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  obtain ⟨lp,_,_,_,_,bill,fee⟩ := strict_high_gap_fixed_successor F paid P E hp credit gap
  change 0<l at lp
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at bill
  change (X.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(rowEnergy F.n F.m (r+i):ℤ)+P.gamma h+((D:ℤ)-H-3)*i at fee
  have priced := total_fixed_platform_price (D:=D) (H:=H) C F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (show F.r≤r+i by dsimp only [r];omega) (show diagonal F.n F.m (F.r+2)≤D+1 by dsimp only [D];omega)
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) head (size ▸ ratio) (size ▸ lp)
  rw [size] at priced
  change rowEnergy F.n F.m (r+i)≤rowEnergy n m (r+i+l)+∑j∈Finset.range (D+1),protectedColumnFee Z N H j at priced
  have all := protected_fee_pays_whole_gap D H Z N i head gap ratio (Nat.sub_le _ _)
  have natural : ((D-H-3:ℕ):ℤ)=(D:ℤ)-H-3 := by omega
  let total : ℕ := ∑j∈Finset.range (D+1),protectedColumnFee Z N H j
  change rowEnergy F.n F.m (r+i)≤rowEnergy n m (r+i+l)+total at priced
  change total+(D-H-3)*i≤D*Z at all
  have cap : (total:ℤ)+((D:ℤ)-H-3)*i≤(D:ℤ)*Z := by
    rw [←natural];exact_mod_cast all
  omega

#print axioms strict_original_head_gap_at_most_seven
end JSP452Audit.StarHost
