import FixedOriginalWinningPairsGiveAnActualArrowAfterTheLaterDeletion
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem true_three_head_exposure {A:Type u} [Finite A] (X:SimpleGraph A) (H w:ℕ) (head:3≤H)
    (cap:∀v,Nat.card (X.neighborSet v)≤H+1) (actual:ExactTypedWidth X H 3 w) :
    H*w≤2*minimumExposure X (H+1) := by
  rcases actual with zero|⟨u,v,up,vp,rank,force⟩
  · rw [zero,Nat.mul_zero];omega
  by_cases odd:H%2=1
  · let k := H/2
    have ht : 2*k+1=H := by dsimp only [k];omega
    have one := forces_uniform_subforests X (fun _:Fin u => H) (fun _:Fin v => 3) H 3 1 1 (by simpa using (show 1≤u by omega)) (by simpa using (show 1≤v by omega)) force
    have clash := no_odd_odd_star_corner X k 1 (by intro z;have := cap z;dsimp only [k];omega)
      (by rw [ht];exact one)
    exact clash.elim
  · let p := H-1
    have sum : p+2=H+1 := by dsimp only [p];omega
    have red : p+1=H := by dsimp only [p];omega
    have bounds (z:A) : Nat.card (X.neighborSet z)≤(H-1)+(3-1) := (cap z).trans_eq sum.symm
    obtain ⟨S,T,apart,need⟩ := original_uniform_factor_cut X H 3 u v (by omega) (by decide) up vp bounds force
    have peak : OriginalUniformPeak X w p 2 := ⟨u,v,up,vp,rank,by rw [red];exact force,S,T,apart,by rw [←rank];exact need⟩
    have cost := (odd_original_peak_exposure peak sum (by dsimp only [p];omega) (by decide) (by decide) cap).2
    simpa only [Nat.add_sub_cancel] using cost

theorem highest_exposure_selector_price {A:Type u} [Finite A] (G:SimpleGraph A) {s t r N q:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (row:ForcingRow G s t (padDemand n) (padDemand m) r)
    (live:0<rowCount s t r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (degree:2≤q) (cap:∀z,Nat.card (G.neighborSet z)≤q) :
    let rho := minimumExposure G q
    let gain := (G.edgeSet.ncard:ℤ)-rowEnergy n m r
    2*((q:ℤ)-2)*rho-(q:ℤ)*(q+2)≤4*gain := by
  intro rho gain
  have ceiling := live_row_height_at_degree_cap G hs ht n m hn hm pn pm row live cap
  have price := universal_selector_price hs ht n m hn hm pn pm G r q N row live smaller paid cap ceiling
  have exposed := (original_width_le_deletion hs ht n m hn hm pn pm G r q row (by omega)).trans (deletionBudget_le_minimumExposure G q (by omega) cap)
  let p := q/2
  have lower : (((q:ℤ)*rho+1)/2)-(p:ℤ)*(p+1)-rho≤gain := by
    change widthAt n m r (q+1)≤rho at exposed
    change (rowEnergy n m r:ℤ)+max 0 ((((q:ℤ)*rho+1)/2)-(p:ℤ)*(p+1)-widthAt n m r (q+1))≤G.edgeSet.ncard at price
    dsimp only [gain];omega
  have half : (2:ℤ)*p≤q := by dsimp only [p];omega
  have lo : 4*(p:ℤ)*(p+1)≤(q:ℤ)*(q+2) := calc
    4*(p:ℤ)*(p+1)=(2*p)*(2*p+2) := by ring
    _ ≤ _ := mul_le_mul half (by omega) (by positivity) (by positivity)
  have twice : (q:ℤ)*rho≤2*(((q:ℤ)*rho+1)/2) := by omega
  linarith only [lower,lo,twice]

#print axioms true_three_head_exposure
#print axioms highest_exposure_selector_price
end JSP452Audit.StarHost
