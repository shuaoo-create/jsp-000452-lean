import EveryOriginalNonpeakCandidateIsPaidByTheSameFixedLists
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_four_five_signed_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let r := F.r+P.cutRoots.ncard
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let N := P.paidCore.ncard
    let l := N/6
    let i := l-(r+1)
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    H+4≤D → 7≤H → 0<l ∧ rowEnergy n m (r+i+l)≤X.edgeSet.ncard ∧
      (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)+((D:ℤ)-H-1)*P.capacity+4*l+1 ≤
       P.gamma h+2*threeSmallCaps N+((D:ℤ)-H-3)*l+3*i := by
  intro D H h r C Y N l i X n m gap head
  let Z := P.capacity
  let cap := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have low : 11≤D := strict_source_degree_at_least_eleven F paid
  have rank : D*P.positives.ncard≤2*Z := by exact_mod_cast cap.2.2.2.1
  have lim := (Nat.mul_le_mul_right P.positives.ncard low).trans rank
  have order := cap.2.2.2.2.2
  change N=2*Z+P.positives.ncard at order
  have fit : 11*N≤24*Z := by omega
  have nonempty : 0<P.positives.ncard := by
    have wt := cap.2.2.1
    have pos : 0<P.weight := by dsimp only [ScaledPortPlan.gamma] at credit;omega
    by_contra! no
    rw [show P.positives.ncard=0 by omega] at wt;push_cast at wt;omega
  have many := (Nat.mul_le_mul_left D nonempty).trans rank
  have lp : 0<l := by dsimp only [l];omega
  have lz : l≤Z := by dsimp only [l];omega
  let U := peakPrefix Y i
  have phase := (four_gap_expensive_prefix F paid P E hp credit gap).2 i (Nat.sub_le _ _)
  obtain ⟨sz,cost⟩ := phase
  change U.ncard=i at sz
  change X.edgeSet.ncard+(D-3)*i≤Y.edgeSet.ncard at cost
  have fixed := paid_fixed_exterior_cut F paid P U l lp lz (by rw [sz];exact Nat.sub_le _ _)
    (by rw [sz];change l≤r+i+1;dsimp only [i];omega)
  have bill := fixed.2.2.2
  change rowEnergy n m (r+U.ncard+l)≤X.edgeSet.ncard at bill;rw [sz] at bill
  refine ⟨lp,bill,?_⟩
  let area := ∑j∈Finset.range D,widthAt F.n F.m (r+i) (j+1)
  let sum := ∑j∈Finset.range D,middleColumnFee Z N H j
  have price := original_physical_truncated_profile F paid P i
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(area:ℤ)+P.gamma h+(D:ℤ)*i at price
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  have loss := truncated_fixed_platform_price (b:=r+i) (D:=D) (H:=H) C F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) head (size ▸ fit) (size ▸ lp)
  rw [size] at loss
  change area≤rowEnergy n m (r+i+l)+sum at loss
  have finite := lower_nonpeak_fee_sum D H Z N head gap fit
  change sum+4*l=(H+1)*Z+2*threeSmallCaps N+(D-H-3)*l at finite
  have fees : (sum:ℤ)+4*l=((H:ℤ)+1)*Z+2*threeSmallCaps N+((D:ℤ)-H-3)*l := by
    rw [←show ((D-H-3:ℕ):ℤ)=(D:ℤ)-H-3 by omega];exact_mod_cast finite
  have steps : (X.edgeSet.ncard:ℤ)+((D:ℤ)-3)*i≤Y.edgeSet.ncard := by
    rw [←show ((D-3:ℕ):ℤ)=(D:ℤ)-3 by omega];exact_mod_cast cost
  have charged : (area:ℤ)≤(rowEnergy n m (r+i+l):ℤ)+sum := by exact_mod_cast loss
  change _+((D:ℤ)-H-1)*Z+_+_≤_
  linarith only [charged,price,fees,steps]

#print axioms strict_four_five_signed_price
end JSP452Audit.StarHost
