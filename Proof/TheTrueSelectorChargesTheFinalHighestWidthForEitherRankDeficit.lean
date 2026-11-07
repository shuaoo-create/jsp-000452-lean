import RetainBothRootCreditsAtEveryRealParityAndEverySize
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ScaledPortPlan.positive_count_with_original_roots {A:Type u} [Finite A] {G:SimpleGraph A} {D k c:ℕ}
    {K:DegreeRegion G D} (P:ScaledPortPlan K k c) (E:PortGraphLayers P) :
    P.positives.ncard≤P.cutRoots.ncard+P.excess := by
  have sub : P.positives⊆P.wholeFamily := fun _ h => h.1
  have count := Set.ncard_le_ncard sub
  change _≤(Subtype.val '' P.family).ncard at count
  rw [Set.ncard_image_of_injective _ Subtype.val_injective,(P.exact_excess E).1] at count
  exact count

theorem highest_width_selector_price {A:Type u} [Finite A] (G:SimpleGraph A) {s t r N q:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (live:0<rowCount s t r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (degree:2≤q) (cap:∀z,Nat.card (G.neighborSet z)≤q) :
    let w := widthAt n m r (q+1)
    let gain := (G.edgeSet.ncard:ℤ)-rowEnergy n m r
    2*((q:ℤ)-2)*w-(q:ℤ)*(q+2)≤4*gain := by
  intro w gain
  have ceiling := live_row_height_at_degree_cap G hs ht n m hn hm pn pm row live cap
  have price := universal_selector_price hs ht n m hn hm pn pm G r q N row live smaller paid cap ceiling
  have exposed := (original_width_le_deletion hs ht n m hn hm pn pm G r q row (by omega)).trans
    (deletionBudget_le_minimumExposure G q (by omega) cap)
  let rho := minimumExposure G q
  let p := q/2
  have weight : (q:ℤ)*w≤(q:ℤ)*rho := by exact_mod_cast Nat.mul_le_mul_left q exposed
  have lower : (((q:ℤ)*rho+1)/2)-(p:ℤ)*(p+1)-w≤gain := by
    change (rowEnergy n m r:ℤ)+max 0 ((((q:ℤ)*rho+1)/2)-(p:ℤ)*(p+1)-w)≤G.edgeSet.ncard at price
    dsimp only [gain];omega
  have half : (2:ℤ)*p≤q := by dsimp only [p];omega
  have lo : 4*(p:ℤ)*(p+1)≤(q:ℤ)*(q+2) := calc
    4*(p:ℤ)*(p+1)=(2*p)*(2*p+2) := by ring
    _ ≤ (q:ℤ)*(q+2) := mul_le_mul half (by omega) (by positivity) (by positivity)
  have twice : (q:ℤ)*rho≤2*(((q:ℤ)*rho+1)/2) := by omega
  linarith only [lower,lo,twice,weight]

#print axioms ScaledPortPlan.positive_count_with_original_roots
#print axioms highest_width_selector_price
end JSP452Audit.StarHost
