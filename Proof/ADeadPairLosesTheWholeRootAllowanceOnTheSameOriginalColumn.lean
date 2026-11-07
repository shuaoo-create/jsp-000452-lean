import AHighGapTwoPlatformCanKeepAtMostTwoPositiveWholeCores
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem positive_monochrome_or_two_root_bounded_counts {A B:Type u} [Finite A] [Finite B] (O:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y j:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) (win:WinsHeight n m r j x y) (pos:0<widthAt n m r j) :
    ExactTypedWidth O x y (widthAt n m r j-Nat.card B/(min x y+1)) ∨
      widthAt n m r j+(r+1)≤Nat.card B/(x+1)+Nat.card B/(y+1) := by
  obtain ⟨px,py,ht,rf,bg,span⟩ := win
  let a := Nat.card B/(x+1)
  let b := Nat.card B/(y+1)
  let M := Nat.card B/(min x y+1)
  have A' : UniformPackCap C x a := fun z copy => ((genuine_uniform_pack_cap C x px) z copy).trans (Nat.min_le_right _ _)
  have B' : UniformPackCap C y b := fun z copy => ((genuine_uniform_pack_cap C y py) z copy).trans (Nat.min_le_right _ _)
  have aM : a≤M := Nat.div_le_div_left (by omega) (by omega)
  have bM : b≤M := Nat.div_le_div_left (by omega) (by omega)
  change ExactTypedWidth O x y (widthAt n m r j-M) ∨ widthAt n m r j+(r+1)≤a+b
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

#print axioms positive_monochrome_or_two_root_bounded_counts
end JSP452Audit.StarHost