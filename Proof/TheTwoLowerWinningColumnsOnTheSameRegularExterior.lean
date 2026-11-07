import TheEvenRegularBlockPaysTheHighestNonpeakColumnWithoutAnyHole
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem monochrome_or_two_bounded_counts {A B:Type u} [Finite A] [Finite B] (O:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y j:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) (win:WinsHeight n m r j x y) :
    ExactTypedWidth O x y (widthAt n m r j-Nat.card B/(min x y+1)) ∨
      widthAt n m r j≤Nat.card B/(x+1)+Nat.card B/(y+1) := by
  obtain ⟨px,py,ht,rf,bg,span⟩ := win
  let a := Nat.card B/(x+1)
  let b := Nat.card B/(y+1)
  let M := Nat.card B/(min x y+1)
  have A' : UniformPackCap C x a := fun z copy => ((genuine_uniform_pack_cap C x px) z copy).trans (Nat.min_le_right _ _)
  have B' : UniformPackCap C y b := fun z copy => ((genuine_uniform_pack_cap C y py) z copy).trans (Nat.min_le_right _ _)
  have aM : a≤M := Nat.div_le_div_left (by omega) (by omega)
  have bM : b≤M := Nat.div_le_div_left (by omega) (by omega)
  change ExactTypedWidth O x y (widthAt n m r j-M) ∨ widthAt n m r j≤a+b
  by_cases red:a<originalThresholdCount n x
  · have seen := palette_retains_typed_rectangle O C C le_rfl n m hn hm px py A'
      (by rw [sdiff_self];exact uniform_pack_bot_cap y py) red bg row
    rw [←span,Nat.sub_zero] at seen
    exact Or.inl (actual_typed_width_down _ seen (by omega))
  by_cases blue:b<originalThresholdCount m y
  · have seen := palette_retains_typed_rectangle O C C le_rfl m n hm hn py px B'
      (by rw [sdiff_self];exact uniform_pack_bot_cap x px) blue rf (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m y),←span,Nat.sub_zero] at seen
    exact Or.inl (actual_typed_width_down _ (exact_typed_width_swap _ seen) (by omega))
  exact Or.inr (by omega)

theorem true_odd_cap_extra_width {A:Type u} [Finite A] (X:SimpleGraph A) (D x y w:ℕ) (odd:D%2=1)
    (rx:4≤x) (byh:4≤y) (height:x+y-1=D+1) (cap:∀v,Nat.card (X.neighborSet v)≤D)
    (real:ExactTypedWidth X x y w) (pos:0<w) : w+2≤minimumExposure X D := by
  rcases real with dead|⟨u,v,up,vp,rank,force⟩
  · omega
  have oriented (a b s t:ℕ) (hs:0<s) (ht:0<t) (h0:s+t-1=w) (ea:a%2=0) (ob:b%2=1) (la:4≤a) (lb:4≤b)
      (sum:a+b-1=D+1) (seen:Forces X (forest (fun _:Fin s => a)) (forest (fun _:Fin t => b))) : w+2≤minimumExposure X D := by
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
  · exact oriented x y u v up vp rank first (by omega) rx byh height force
  · exact oriented y x v u vp up (by omega) (by omega) (by omega) byh rx (by omega) (forces_swap force)

#print axioms monochrome_or_two_bounded_counts
#print axioms true_odd_cap_extra_width
end JSP452Audit.StarHost
