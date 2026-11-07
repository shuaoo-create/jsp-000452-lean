import AColdLastVertexOrAnExtraPaidEdgeClosesTheFourthGap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem peak_prefix_spends_at_least {V:Type u} [Finite V] (G:SimpleGraph V) (i d:ℕ) (peak:d≤peakFee G i) :
    d*i≤∑j∈Finset.range i,peakFee G j := calc
  d*i=∑_j∈Finset.range i,d := by simp [Nat.mul_comm]
  _ ≤ _ := Finset.sum_le_sum (fun j hj => peak.trans (peak_fee_antitone G (Finset.mem_range.mp hj).le))

set_option maxHeartbeats 600000 in
theorem strict_original_head_gap_at_most_three (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    D-H≤3 := by
  intro D H
  have top := strict_original_head_gap_at_most_four F paid
  change D-H≤4 at top
  by_contra! large
  have eq : D=H+4 := by omega
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  have head : 7≤H := by omega
  obtain ⟨K,k,c,P,_,⟨E⟩,hp,rp,signed,_⟩ := strict_high_two_term_original_package F paid
  let h := highestWidth F.n F.m F.r
  change 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 at signed
  have credit : P.gamma h≤0 := by
    have a := mul_nonneg (show (0:ℤ)≤(D:ℤ)+2 by omega) (show (0:ℤ)≤P.excess by positivity)
    have b := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤h by positivity)
    omega
  let Z := P.capacity
  let c₀ := P.positives.ncard
  let N := P.paidCore.ncard
  let C := F.G.induce P.paidCore
  let Y := F.G.induce P.exterior
  let r := F.r+P.cutRoots.ncard
  let R := r+1
  let l := N/6
  let i := l-R
  let U := peakPrefix Y i
  let X := Y.induce Uᶜ
  let n := fixedCoreList C F.n l
  let m := fixedCoreList C F.m l
  let g : ℤ := (X.edgeSet.ncard:ℤ)-rowEnergy n m (r+i+l)
  let w := widthAt n m (r+i+l) (D-2)
  have a := P.exact_weight_and_root_cost E (minimal_rank_exact_source F paid).2.2.2.1 h
  have order := a.2.2.2.2.2
  change N=2*Z+c₀ at order
  have vol : D*c₀≤2*Z := by exact_mod_cast a.2.2.2.1
  have count := (Nat.mul_le_mul_right c₀ deg).trans vol
  have room := P.positive_count_with_original_roots E
  have pieces : c₀+1≤R+P.excess := by dsimp only [c₀,R,r];omega
  have gap : H+4≤D := eq.ge
  obtain ⟨lp,bill,bound⟩ := strict_four_five_signed_price F paid P E hp credit gap head
  change 0<l at lp
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at bill
  have baseline : 0≤g := by dsimp only [g];omega
  change g+((D:ℤ)-H-1)*Z+4*l+1≤P.gamma h+2*threeSmallCaps N+((D:ℤ)-H-3)*l+3*i at bound
  rw [show (D:ℤ)-H-1=3 by omega,show (D:ℤ)-H-3=1 by omega,one_mul] at bound
  have long := gap_four_fixed_width F paid P E hp credit gap lp i
  change Z+1≤w+i+N/4 at long
  have exclude := fourth_gap_price_alternatives D Z c₀ P.excess h R w (P.gamma h) g deg (by omega) hp
    (by dsimp only [R];omega) pieces count (by omega) baseline
  dsimp only at exclude
  rw [←order] at exclude
  change (g+3*Z+3*l+1≤P.gamma h+2*threeSmallCaps N+3*i) → _ at exclude
  apply exclude (by omega) long
  by_cases expensive:D-2≤peakFee Y i
  · left
    have saving := peak_prefix_spends_at_least Y i (D-2) expensive
    have extra : X.edgeSet.ncard+(D-3)*i+i≤Y.edgeSet.ncard := by
      have plus : (D-2)*i=(D-3)*i+i := by rw [←Nat.succ_mul];congr 1;omega
      rw [peak_prefix_edge_account Y i]
      change (Y.induce (peakPrefix Y i)ᶜ).edgeSet.ncard+_+_≤_;omega
    have strong := (strict_four_five_price_with_extra_edges F paid P E hp credit i extra gap head).2.2
    change g+((D:ℤ)-H-1)*Z+4*l+1+i≤P.gamma h+2*threeSmallCaps N+((D:ℤ)-H-3)*l+3*i at strong
    rw [show (D:ℤ)-H-1=3 by omega,show (D:ℤ)-H-3=1 by omega,one_mul] at strong
    change g+3*Z+3*l+1+i≤P.gamma h+2*threeSmallCaps N+3*i
    omega
  · right
    have low (v:↥(Uᶜ:Set ↥P.exterior)) : Nat.card (X.neighborSet v)≤D-3 := by
      have below := (chosenPeakStep Y U).cap v
      change Nat.card (X.neighborSet v)≤peakFee Y i at below;omega
    have size := ((four_gap_expensive_prefix F paid P E hp credit gap).2 i (Nat.sub_le _ _)).1
    change U.ncard=i at size
    have lz : l≤Z := by dsimp only [l];omega
    have data := paid_fixed_exterior_cut F paid P U l lp lz (by rw [size];exact Nat.sub_le _ _)
      (by rw [size];change l≤r+i+1;dsimp only [i,R];omega)
    obtain ⟨live,smaller,row,_⟩ := data
    rw [size] at live smaller row
    have hs := F.hs
    have ht := F.ht
    have charge := highest_width_selector_price X (q:=D-3)
      (show 0<min F.s ((componentBudget C F.n).len+l) by omega)
      (show 0<min F.t ((componentBudget C F.m).len+l) by omega) n m
      (protected_demand_antitone F.n _ F.hn ((componentBudget C F.n).entries_antitone _ F.hn) l)
      (protected_demand_antitone F.m _ F.hm ((componentBudget C F.m).entries_antitone _ F.hm) l)
      (protected_demand_positive F.n _ F.pn ((componentBudget C F.n).entries_positive _ F.pn) l)
      (protected_demand_positive F.m _ F.pm ((componentBudget C F.m).entries_positive _ F.pm) l)
      row live smaller paid (by omega) low
    change 2*(((D-3:ℕ):ℤ)-2)*widthAt n m (r+i+l) (D-3+1)-((D-3:ℕ):ℤ)*(((D-3:ℕ):ℤ)+2)≤4*g at charge
    rw [show D-3+1=D-2 by omega,show ((D-3:ℕ):ℤ)=(D:ℤ)-3 by omega] at charge
    exact charge

#print axioms peak_prefix_spends_at_least
#print axioms strict_original_head_gap_at_most_three
end JSP452Audit.StarHost
