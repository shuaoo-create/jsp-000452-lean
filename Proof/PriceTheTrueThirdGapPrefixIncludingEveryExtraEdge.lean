import CompareAllTheActualThirdGapHeightsWithTheirFixedSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem third_platform_price_with_extra_edges (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    (E:PortGraphLayers P) (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤0) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let r := F.r+P.cutRoots.ncard
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let N := P.paidCore.ncard
    let l := N/5
    let i := l-(r+1)
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    ∀b:ℕ,X.edgeSet.ncard+(D-2)*i+b≤Y.edgeSet.ncard → D=H+3 → P.capacity<widthAt F.n F.m r (D-1) → 0<l ∧ rowEnergy n m (r+i+l)≤X.edgeSet.ncard ∧
      (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)+((D:ℤ)-H-1)*P.capacity+3*l+1+b ≤
       P.gamma h+2*(N/3+N/4:ℕ)+((D:ℤ)-H-2)*l+2*i := by
  intro D H h r C Y N l i X n m b extra gap high
  have head : 8≤H := by have deg : 11≤D := strict_source_degree_at_least_eleven F paid;omega
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
  obtain ⟨_,_,_,_,_,_,hist⟩ := third_gap_high_platform F paid P E hp credit gap high
  have phase := hist i (Nat.sub_le _ _)
  obtain ⟨sz,_⟩ := phase
  change U.ncard=i at sz
  have fixed := paid_fixed_exterior_cut F paid P U l lp lz (by rw [sz];exact Nat.sub_le _ _)
    (by rw [sz];change l≤r+i+1;dsimp only [i];omega)
  have bill := fixed.2.2.2
  change rowEnergy n m (r+U.ncard+l)≤X.edgeSet.ncard at bill;rw [sz] at bill
  refine ⟨lp,bill,?_⟩
  let area := ∑j∈Finset.range D,widthAt F.n F.m (r+i) (j+1)
  let sum := ∑j∈Finset.range D,thirdColumnFee Z N H j
  have price := original_physical_truncated_profile F paid P i
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤(area:ℤ)+P.gamma h+(D:ℤ)*i at price
  have size : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  have loss := third_fixed_platform_price (b:=r+i) (D:=D) (H:=H) C F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (Nat.le_max_left _ _) (Nat.le_max_right _ _) head (size ▸ fit) (size ▸ lp)
  rw [size] at loss
  change area≤rowEnergy n m (r+i+l)+sum at loss
  have finite := third_nonpeak_fee_sum D H Z N head (by omega) fit
  change sum+3*l=(H+1)*Z+2*(N/3+N/4:ℕ)+(D-H-2)*l at finite
  have fees : (sum:ℤ)+3*l=((H:ℤ)+1)*Z+2*(N/3+N/4:ℕ)+((D:ℤ)-H-2)*l := by
    rw [←show ((D-H-2:ℕ):ℤ)=(D:ℤ)-H-2 by omega];exact_mod_cast finite
  have steps : (X.edgeSet.ncard:ℤ)+((D:ℤ)-2)*i+b≤Y.edgeSet.ncard := by
    rw [←show ((D-2:ℕ):ℤ)=(D:ℤ)-2 by omega];exact_mod_cast extra
  have charged : (area:ℤ)≤(rowEnergy n m (r+i+l):ℤ)+sum := by exact_mod_cast loss
  change _+((D:ℤ)-H-1)*Z+_+_+_≤_
  linarith only [charged,price,fees,steps]

#print axioms third_platform_price_with_extra_edges
end JSP452Audit.StarHost
