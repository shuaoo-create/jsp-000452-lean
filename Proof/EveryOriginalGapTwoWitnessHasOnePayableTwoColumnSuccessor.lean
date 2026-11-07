import TheOriginalGapTwoProfileLeavesExactlyTwoPricedColumns
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem gap_two_original_witness (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
    let h := highestWidth F.n F.m F.r
    D=H+2 → ∃(K:DegreeRegion F.G D) (k c:ℕ) (P:ScaledPortPlan K k c),0<k ∧ Nonempty (PortGraphLayers P) ∧
      0<h ∧ h≤P.excess ∧ P.gamma h≤-3*(P.excess:ℤ) ∧
      (4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0) ∧
      (D%2=1 → h+1≤P.excess ∧ 4*P.gamma h+((D:ℤ)+3)*P.excess+((D:ℤ)-5)*h+2*P.beta≤0) ∧
      (P.excess=1 → D%2=0 ∧ h=1 ∧ (oddRegularComponents F.G D).ncard=1 ∧ P.shortfall=0) ∧
      (let Y := F.G.induce P.exterior
       let r := F.r+P.cutRoots.ncard
       let i := P.capacity-(r+1)
       let W := widthAt F.n F.m r
       let u := peakCountAbove Y H
       let b := peakCountAbove Y (H+1)
       let X := Y.induce (peakPrefix Y i)ᶜ
       let g := X.edgeSet.ncard-rowEnergy F.n F.m (r+i+P.capacity)
       r+1<P.capacity ∧ i < peakCountAbove Y (H-1) ∧ b < i ∧ P.capacity<W (H+1) ∧
       ForcingRow X F.s F.t (padDemand F.n) (padDemand F.m) (r+i+P.capacity) ∧
       0<rowCount F.s F.t (r+i+P.capacity) ∧ rowCount F.s F.t (r+i+P.capacity)<F.rank ∧
       (i ≤ u → (g:ℤ)+P.capacity+b+1≤(W D:ℤ)+P.gamma h) ∧
       (u < i → (g:ℤ)+2*P.capacity+b+1≤(W (H+1):ℤ)+P.paidCore.ncard/4+minimumExposure (F.G.induce P.paidCore) D+P.gamma h)) := by
  intro D H h gap
  obtain ⟨K,k,c,P,kl,⟨E⟩,hp,hρ,sharp,odd,one⟩ := strict_original_credit_and_singleton F paid
  have deg : 11≤D := strict_source_degree_at_least_eleven F paid
  change 4*P.gamma h+((D:ℤ)+2)*P.excess+((D:ℤ)-6)*h+2*P.beta≤0 at sharp
  have weight := mul_nonneg (show (0:ℤ)≤(D:ℤ)-10 by omega) (show (0:ℤ)≤P.excess by positivity)
  have head := mul_nonneg (show (0:ℤ)≤(D:ℤ)-6 by omega) (show (0:ℤ)≤h by positivity)
  have credit : P.gamma h≤-3*(P.excess:ℤ) := by linarith only [sharp,weight,head,show (0:ℤ)≤P.beta by positivity]
  obtain ⟨big,_,stock⟩ := gap_two_initial_inventory F paid P E kl hp credit gap
  obtain ⟨row,pos,small,_,wide,short,high,low⟩ := gap_two_last_two_prices F paid P E kl hp credit gap
  refine ⟨K,k,c,P,kl,⟨E⟩,hp,hρ,credit,sharp,odd,one,big,stock,short,wide,row,pos,small,?_,low⟩
  intro enough
  have close := high enough
  change _≤(widthAt F.n F.m (F.r+P.cutRoots.ncard) D:ℤ)+P.gamma h
  simpa only [gap] using close

#print axioms gap_two_original_witness
end JSP452Audit.StarHost