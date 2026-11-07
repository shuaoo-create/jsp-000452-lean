import ShortStageInOddEvenRegularComponent
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem smaller_row_exposure_budget {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    {X:Type u} [Finite X] (G:SimpleGraph X) (r D N:ℕ) (positive:0<D)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (live:0<rowCount s t r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (height:diagonal n m (r+2)≤D+1) :
    ((D:ℤ)-2)*(minimumExposure G D:ℤ)≤2*((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)+
      2*((G.edgeSet.ncard:ℤ)-(rowEnergy n m r:ℤ)) := by
  let h := widthAt n m r (D+1)
  let rho := minimumExposure G D
  have width : h≤rho := (widthAt_le_uniformEnvelope hs ht n m hn hm pn pm G r (D+1) row (by omega)).trans
    ((uniformEnvelope_le_deletion G D positive).trans (deletionBudget_le_minimumExposure G D positive cap))
  have fee := universal_selector_price hs ht n m hn hm pn pm G r D N row live smaller paid cap height
  have left := le_max_right (0:ℤ) (selectorTarget G D-(h:ℤ))
  change (rowEnergy n m r:ℤ)+max 0 (selectorTarget G D-(h:ℤ))≤(G.edgeSet.ncard:ℤ) at fee
  change ((D:ℤ)*(rho:ℤ)+1)/2-((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)-(h:ℤ)≤_ at left
  change ((D:ℤ)-2)*(rho:ℤ)≤_
  rw [sub_mul,mul_assoc 2]
  omega

theorem smaller_row_seven_exposure_budget {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    {X:Type u} [Finite X] (G:SimpleGraph X) (r N:ℕ)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (live:0<rowCount s t r) (smaller:rowCount s t r<N)
    (paid:AllSmallerPaid.{u} N) (cap:∀v,Nat.card (G.neighborSet v)≤7) (height:diagonal n m (r+2)≤8) :
    5*(minimumExposure G 7:ℤ)≤24+2*((G.edgeSet.ncard:ℤ)-(rowEnergy n m r:ℤ)) := by
  have actual := smaller_row_exposure_budget hs ht n m hn hm pn pm G r 7 N (by decide) row live smaller paid cap height
  norm_num at actual
  exact actual

#print axioms smaller_row_exposure_budget
#print axioms smaller_row_seven_exposure_budget
end JSP452Audit.StarHost
