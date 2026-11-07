import TheSamePayablePeakHistoryRetainsItsActualSuccessorSurplus
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_last_two_prices (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) (kl:0<k)
    (hp:0<highestWidth F.n F.m F.r) (credit:P.gamma (highestWidth F.n F.m F.r)≤-3*(P.excess:ℤ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let Y := F.G.induce P.exterior
    let r := F.r+P.cutRoots.ncard
    let Z := P.capacity
    let i := Z-(r+1)
    let W := widthAt F.n F.m r
    let U := peakPrefix Y i
    let g := (Y.induce Uᶜ).edgeSet.ncard-rowEnergy F.n F.m (r+i+Z)
    let u := peakCountAbove Y H
    let b := peakCountAbove Y (H+1)
    let G := P.gamma (highestWidth F.n F.m F.r)
    D=H+2 →
      ForcingRow (Y.induce Uᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (r+i+Z) ∧
      0<rowCount F.s F.t (r+i+Z) ∧ rowCount F.s F.t (r+i+Z)<F.rank ∧
      (g:ℤ)+2*Z+(min i u:ℕ)+(min i b:ℕ)+1≤(min (i+Z) (W (H+1)):ℕ)+(min (i+Z) (W (H+2)):ℕ)+G ∧
      Z<W (H+1) ∧ b < i ∧
      (i ≤ u → (g:ℤ)+Z+b+1≤(W (H+2):ℤ)+G) ∧
      (u < i → (g:ℤ)+2*Z+b+1≤(W (H+1):ℤ)+P.paidCore.ncard/4+minimumExposure (F.G.induce P.paidCore) D+G) := by
  intro D H Y r Z i W U g u b G gap
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  obtain ⟨big,small,stock⟩ := gap_two_initial_inventory F paid P E kl hp credit gap
  change r+1<Z at big
  change i < peakCountAbove Y (H-1) at stock
  obtain ⟨_,_,_,_,zp,room,caps⟩ := full_capacity_prefix_data F paid P E hp (by omega)
  have fits (Q:↥P.positives) : matchingEdges Q.val.toSimpleGraph≤r+i+1 :=
    (caps Q).trans (by change Z≤r+(Z-(r+1))+1;omega)
  obtain ⟨row,raw⟩ := strict_peak_history_with_actual_surplus F paid P i ((Nat.sub_le _ _).trans room)
    (by omega) fits
  change (g:ℤ)+(D:ℤ)*Z+(∑j∈Finset.range D,min i (peakCountAbove Y j):ℕ)+1≤
    (∑j∈Finset.range D,min (i+Z) (W (j+1)):ℕ)+G at raw
  have init : (∑j∈Finset.range H,min i (peakCountAbove Y j))=H*i := by
    calc
      _ = ∑_j∈Finset.range H,i := Finset.sum_congr rfl (fun j hj => min_eq_left
        (stock.le.trans (peak_counts_antitone Y (by have := Finset.mem_range.mp hj;omega))))
      _ = _ := by simp
  have upper : (∑j∈Finset.range H,min (i+Z) (W (j+1)))≤H*(i+Z) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] using
      Finset.sum_le_sum (s:=Finset.range H) (fun j _ => Nat.min_le_left (i+Z) (W (j+1)))
  rw [gap,show H+2=H+1+1 by omega,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,Finset.sum_range_succ,init] at raw
  push_cast at raw
  rw [Nat.mul_add] at upper
  have cost : (g:ℤ)+2*Z+(min i u:ℕ)+(min i b:ℕ)+1≤(min (i+Z) (W (H+1)):ℕ)+(min (i+Z) (W (H+2)):ℕ)+G := by
    have cap : ((∑j∈Finset.range H,min (i+Z) (W (j+1)):ℕ):ℤ)≤(H:ℤ)*i+(H:ℤ)*Z := by exact_mod_cast upper
    push_cast at cap ⊢
    dsimp only [u,b];linarith only [raw,cap]
  have lower := (strict_payable_exterior_constraints F paid P).1
  change Z+r+(F.rank-matchingEdges F.G)+1≤min F.s F.t at lower
  have lim := (strict_payable_exterior_constraints F paid P).2.1
  change max F.s F.t≤matchingEdges Y at lim
  have zD := (strict_payable_exterior_constraints F paid P).2.2.1
  have length := (strict_payable_exterior_constraints F paid P).2.2.2.1
  change rowCount F.s F.t r=Z+matchingEdges Y+(F.rank-matchingEdges F.G) at length
  have more : i < matchingEdges Y+(F.rank-matchingEdges F.G) := by
    have both : min F.s F.t≤max F.s F.t := (min_le_left _ _).trans (le_max_left _ _)
    dsimp only [i];omega
  have original := F.live
  have pos : 0<rowCount F.s F.t (r+i+Z) := by dsimp only [rowCount] at length ⊢;omega
  have smaller : rowCount F.s F.t (r+i+Z)<F.rank := by
    change _<rowCount F.s F.t F.r;dsimp only [r,rowCount] at original ⊢;omega
  have dec : W (H+2)≤W (H+1) := by
    apply Finset.card_le_card;intro j hj
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1,(show H+1≤H+2 by omega).trans (Finset.mem_filter.mp hj).2⟩
  have gb : G≤0 := by dsimp only [G];omega
  have order : b≤u := peak_counts_antitone Y (by omega)
  have left : Z<W (H+1) := by omega
  have low : b < i := by omega
  refine ⟨row,pos,smaller,cost,left,low,fun _ => by omega,?_⟩
  intro short
  have tail := (gap_two_top_typed F paid P E kl gap).2.2.2.2
  change W D≤peakCountAbove Y (D-2)+P.paidCore.ncard/4+minimumExposure (F.G.induce P.paidCore) D at tail
  rw [show D-2=H by omega] at tail
  change W D≤u+P.paidCore.ncard/4+minimumExposure (F.G.induce P.paidCore) D at tail
  have same : W D=W (H+2) := congrArg W gap
  omega

#print axioms gap_two_last_two_prices
end JSP452Audit.StarHost