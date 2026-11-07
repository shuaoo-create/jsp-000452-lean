import WholeCorePrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Liu's complete selector price, including the smaller-rank baseline.
The column width is measured at the allowed degree plus one. -/
theorem universal_selector_price {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type u} [Finite X] (G : SimpleGraph X) (r D N : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : 0<rowCount s t r) (smaller : rowCount s t r<N)
    (paid : AllSmallerPaid.{u} N) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (height : diagonal n m (r+2)≤D+1) :
    (rowEnergy n m r:ℤ)+max 0 (selectorTarget G D-(widthAt n m r (D+1):ℤ)) ≤ (G.edgeSet.ncard:ℤ) := by
  have floor := paid hs ht n m hn hm pn pm G r row smaller
  have base : (rowEnergy n m r:ℤ)≤(G.edgeSet.ncard:ℤ) := by exact_mod_cast floor
  by_cases heavy : 0<selectorTarget G D
  · have hi := selector_positive_price hs ht n m hn hm pn pm G r D N row live smaller.le paid cap height heavy
    omega
  · omega

theorem width_at_peak {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (r : ℕ) :
    widthAt n m r (diagonal n m (r+2))=highestWidth n m r := by
  unfold widthAt highestWidth
  have eq : offsetsAt n m r (diagonal n m (r+2))=highestOffsets n m r := by
    ext i
    simp only [offsetsAt,highestOffsets,Finset.mem_filter,Finset.mem_range]
    apply and_congr_right
    intro hi
    have le := earlier_diagonal_dominates hs ht n m hn hm (show r ≤ r+i by omega)
      (show r+i<s+t-1 by dsimp [rowCount] at hi; omega)
    omega
  rw [eq]

/-- The initial minimal strict source itself cannot appeal to the zero-gain
baseline. Its missing edge instead gives this strict cap on full-degree exposure. -/
theorem minimal_source_exposure_cap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    ((D:ℤ)-2)*(minimumExposure F.G D:ℤ)+2 ≤ 2*((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) := by
  intro D
  obtain ⟨i,j,idx,att⟩ := diagonal_attained F.n F.m F.hs F.ht F.r (by have h:=F.live; dsimp [rowCount] at h; omega)
  have pp := F.pn i
  have qq := F.pm j
  have dh : D+1=diagonal F.n F.m (F.r+2) := by dsimp [D];omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  let h := widthAt F.n F.m F.r (D+1)
  let rho := minimumExposure F.G D
  have eq : h = highestWidth F.n F.m F.r := by
    dsimp [h]; rw [dh,width_at_peak F.hs F.ht F.n F.m F.hn F.hm]
  have lim := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have tax : 1≤h ∧ h≤rho := eq.symm ▸ lim
  have net : selectorTarget F.G D < (h:ℤ) := by
    by_cases pos : 0<selectorTarget F.G D
    · have price := selector_positive_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r D F.rank F.row
        F.live (le_refl _) paid cap dh.ge pos
      have bad : (F.G.edgeSet.ncard:ℤ)<(rowEnergy F.n F.m F.r:ℤ) := by exact_mod_cast F.strict
      change (rowEnergy F.n F.m F.r:ℤ)+_ ≤ _+(h:ℤ) at price
      omega
    · omega
  unfold selectorTarget at net
  change ((D:ℤ)*(rho:ℤ)+1)/2-_ < (h:ℤ) at net
  change ((D:ℤ)-2)*(rho:ℤ)+2 ≤ _
  rw [sub_mul,mul_assoc 2]
  omega
#print axioms universal_selector_price
#print axioms minimal_source_exposure_cap
end JSP452Audit.StarHost