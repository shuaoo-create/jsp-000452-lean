import RefundTheFullOriginalTopPairOnTheSameProtectedProfile
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem last_gap_actual_top_refund (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) (l fee:ℕ) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    let C := F.G.induce P.paidCore
    let Y := F.G.induce P.exterior
    let N := P.paidCore.ncard
    let Z := P.capacity
    let r := F.r+P.cutRoots.ncard
    let i := l-(r+1)
    let X := Y.induce (peakPrefix Y i)ᶜ
    let n := fixedCoreList C F.n l
    let m := fixedCoreList C F.m l
    let g := X.edgeSet.ncard-rowEnergy n m (r+i+l)
    D=H+1 → 0<l → N/6≤l → l≤N/3 →
      widthAt F.n F.m (r+i) D≤widthAt n m (r+i+l) D+fee →
      0<rowCount (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l)) (r+i+l) ∧ rowCount (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l)) (r+i+l)<F.rank ∧
      ForcingRow X (min F.s ((componentBudget C F.n).len+l)) (min F.t ((componentBudget C F.m).len+l))
        (padDemand n) (padDemand m) (r+i+l) ∧
      (g:ℤ)+min i (peakCountAbove Y H)+1+(N/3:ℕ)≤
        P.gamma h+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ)+i+fee := by
  intro D H h C Y N Z r i X n m g gap lp lo hi real
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨_,_,_,ratio,_,room,_⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  change 16*N≤35*Z at ratio
  have lz : l≤Z := by omega
  let U := peakPrefix Y i
  have avail : i≤Nat.card ↥P.exterior := by rw [Nat.card_coe_set_eq];change Z≤P.exterior.ncard at room;dsimp only [i];omega
  have size : U.ncard=i := (peak_prefix_size Y i).trans (min_eq_left avail)
  have fixed := paid_fixed_exterior_cut F paid P U l lp lz (by rw [size];exact Nat.sub_le _ _) (by rw [size];change l≤r+i+1;dsimp only [i];omega)
  rw [size] at fixed
  obtain ⟨pos,smaller,row,bill⟩ := fixed
  refine ⟨pos,smaller,row,?_⟩
  change rowEnergy n m (r+i+l)≤X.edgeSet.ncard at bill
  have actual : X.edgeSet.ncard=rowEnergy n m (r+i+l)+g := by dsimp only [g];omega
  have replen := (gap_one_mixed_refund_stock F paid P E kl hp credit gap).1
  change N/3-(r+1)<peakCountAbove Y (H-1) at replen
  have stock : i≤peakCountAbove Y (H-1) := by dsimp only [i];omega
  have cap (v:↥P.exterior) : Nat.card (Y.neighborSet v)≤D :=
    (induced_neighbor_count_le F.G _ v).trans ((minimal_rank_exact_source F paid).2.2.2.1 v.val)
  have steps := peak_prefix_layer_price Y D i cap
  change Y.edgeSet.ncard=X.edgeSet.ncard+_ at steps
  have init : (∑j∈Finset.range H,min i (peakCountAbove Y j))=H*i := by
    calc
      _ = ∑_j∈Finset.range H,i := Finset.sum_congr rfl (fun j hj => min_eq_left
        (stock.trans (peak_counts_antitone Y (by have := Finset.mem_range.mp hj;omega))))
      _ = _ := by simp
  rw [gap,Finset.sum_range_succ,init] at steps
  let area := ∑j∈Finset.range (H+1),widthAt F.n F.m (r+i) (j+1)
  let tax := ∑j∈Finset.range (H+1),lastGapFixedFee Z N H l j
  have near := original_physical_truncated_profile F paid P i
  change (Y.edgeSet.ncard:ℤ)+(D:ℤ)*Z+1≤((∑j∈Finset.range D,widthAt F.n F.m (r+i) (j+1):ℕ):ℤ)+P.gamma h+(D:ℤ)*i at near
  rw [gap] at near
  change (Y.edgeSet.ncard:ℤ)+((H+1:ℕ):ℤ)*Z+1≤(area:ℤ)+P.gamma h+((H+1:ℕ):ℤ)*i at near
  simp only [Nat.cast_add,Nat.cast_one] at near
  have card : Nat.card ↥P.paidCore=N := Nat.card_coe_set_eq _
  rw [gap] at real
  have close := gap_one_fixed_area_with_real_top_tax (b:=r+i) C F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (Nat.le_max_left _ _)
    (Nat.le_max_right _ _) (by omega : 9≤H) (card ▸ ratio) lp (card ▸ lo) (card ▸ hi) real
  rw [card] at close
  change area+N/3≤rowEnergy n m (r+i+l)+tax+fee at close
  have fees := last_gap_price_sum Z N H l (by omega) ratio lo hi
  change tax=(H+1)*Z+2*(N/3-l)+(N/4-l)+(N/5-l) at fees
  have feeZ : (tax:ℤ)=((H:ℤ)+1)*Z+2*((N/3-l:ℕ):ℤ)+((N/4-l:ℕ):ℤ)+((N/5-l:ℕ):ℤ) := by exact_mod_cast fees
  have paidZ : (area:ℤ)+(N/3:ℕ)≤(rowEnergy n m (r+i+l):ℤ)+tax+fee := by exact_mod_cast close
  have edgeZ : (Y.edgeSet.ncard:ℤ)=(X.edgeSet.ncard:ℤ)+((H:ℤ)*i+min i (peakCountAbove Y H)) := by exact_mod_cast steps
  have succZ : (X.edgeSet.ncard:ℤ)=rowEnergy n m (r+i+l)+(g:ℤ) := by exact_mod_cast actual
  linarith only [feeZ,paidZ,edgeZ,succZ,near]

#print axioms last_gap_actual_top_refund
end JSP452Audit.StarHost