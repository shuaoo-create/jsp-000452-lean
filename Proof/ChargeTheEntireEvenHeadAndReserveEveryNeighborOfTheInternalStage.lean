import BothActualNonpeakColumnsOnTheGapTwoRegularExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_even_head_exposure_at_odd_cap {A:Type u} [Finite A] (X:SimpleGraph A) (D x y w:ℕ) (odd:D%2=1)
    (rx:3≤x) (byh:3≤y) (height:x+y-1=D+1) (cap:∀v,Nat.card (X.neighborSet v)≤D)
    (real:ExactTypedWidth X x y w) (pos:0<w) : w+((if x%2=0 then x else y)-2)≤minimumExposure X D := by
  rcases real with dead|⟨u,v,up,vp,rank,force⟩
  · omega
  have oriented (a b s t:ℕ) (hs:0<s) (ht:0<t) (h0:s+t-1=w) (ea:a%2=0) (ob:b%2=1) (la:4≤a) (lb:3≤b)
      (sum:a+b-1=D+1) (seen:Forces X (forest (fun _:Fin s => a)) (forest (fun _:Fin t => b))) : w+(a-2)≤minimumExposure X D := by
    let p := a-1
    let q := b-1
    have P : p+1=a := by dsimp only [p];omega
    have Q : q+1=b := by dsimp only [q];omega
    have deg : p+q=D := by dsimp only [p,q];omega
    obtain ⟨S,T,dis,need⟩ := original_uniform_factor_cut X a b s t (by omega) (by omega) hs ht (fun z => (cap z).trans_eq deg.symm) seen
    have peak : OriginalUniformPeak X w p q := ⟨s,t,hs,ht,h0,by rw [P,Q];exact seen,S,T,dis,by rw [←h0];exact need⟩
    have bound := (odd_original_peak_exposure peak deg (by dsimp only [p];omega) (by dsimp only [q];omega) (by dsimp only [q];omega) cap).1
    have mult := Nat.mul_le_mul_left (p-1) (show 1≤(w-1)/q+1 from Nat.succ_le_succ (Nat.zero_le _))
    dsimp only [p] at mult bound;omega
  by_cases first:x%2=0
  · rw [if_pos first]
    exact oriented x y u v up vp rank first (by omega) (by omega) byh height force
  · rw [if_neg first]
    exact oriented y x v u vp up (by omega) (by omega) (by omega) (by omega) rx (by omega) (forces_swap force)

theorem independent_stage_reserves_all_neighbors {A:Type u} [Finite A] (C:SimpleGraph A) (q:ℕ) (I:Set A)
    (stage:CompleteDegreeStage C q I) (positive:0<I.ncard) : I.ncard+q≤Nat.card A := by
  obtain ⟨v,mem⟩ := (Set.ncard_pos (Set.toFinite _)).mp positive
  have sub : C.neighborSet v⊆Iᶜ := by
    intro y adj hy
    exact stage.1 mem hy (C.ne_of_adj adj) adj
  have count := Set.ncard_le_ncard sub
  have full := stage.2.1 v mem
  rw [Nat.card_coe_set_eq] at full
  have all := Set.ncard_add_ncard_compl I
  omega

#print axioms full_even_head_exposure_at_odd_cap
#print axioms independent_stage_reserves_all_neighbors
end JSP452Audit.StarHost