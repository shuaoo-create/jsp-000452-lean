import TwoSuccessiveExteriorThresholdsAsActualNestedInducedGraphs
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem even_split_top_red {A B:Type u} [Finite A] [Finite B] (O:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y D:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hs:0<s) (ht:0<t) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r)
    (win:WinsHeight n m r D x y) (even:x%2=0) (odd:y%2=1)
    (cap:∀z,Nat.card (C.neighborSet z)≤D) (heads:D+2≤n ⟨0,hs⟩+m ⟨0,ht⟩) (top:widthAt n m r (D+1)≤1) :
    let M := Nat.card B/(min x y+1)
    ExactTypedWidth O x y (widthAt n m r D-M) := by
  intro M
  obtain ⟨px,py,eq,rf,bg,span⟩ := win
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  have rx : UniformPackCap C x M := fun a copy => ((genuine_uniform_pack_cap C x px a copy).trans (Nat.min_le_right _ _)).trans (Nat.div_le_div_left (by omega) (by omega))
  have by' : UniformPackCap C y M := fun a copy => ((genuine_uniform_pack_cap C y py a copy).trans (Nat.min_le_right _ _)).trans (Nat.div_le_div_left (by omega) (by omega))
  by_cases red:M<f
  · have take := palette_retains_typed_rectangle O C C le_rfl n m hn hm px py rx (by rw [sdiff_self];exact uniform_pack_bot_cap y py) red bg row
    simpa only [span,Nat.sub_zero] using take
  by_cases blue:M<g
  · have take := palette_retains_typed_rectangle O C C le_rfl m n hm hn py px by' (by rw [sdiff_self];exact uniform_pack_bot_cap x px) blue rf
      (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m y),Nat.sub_zero,←span] at take
    exact exact_typed_width_swap O take
  let H := n ⟨0,hs⟩
  have xh : x≤H := (original_threshold_prefix n hn x ⟨0,hs⟩).2 rf
  by_cases larger:x<H
  · have d : 2*(x/2+y/2)=D := by omega
    obtain ⟨R,sub,limits⟩ := even_even_degree_split C (x/2) (y/2) (fun z => (cap z).trans_eq d.symm)
    have first := uniform_pack_below_degree R H (fun z => by have b := (limits z).1;omega)
    have last := uniform_pack_below_degree (C \ R) y (fun z => by have b := (limits z).2;omega)
    have fH : 0<originalThresholdCount n H := (original_threshold_prefix n hn H ⟨0,hs⟩).1 le_rfl
    have take := palette_retains_typed_rectangle O C R sub n m hn hm (by omega : 0<H) py first last fH bg row
    change ExactTypedWidth O H y (originalThresholdCount n H+g-1-r-0-0) at take
    have width : widthAt n m r D=f+g-1-r := span
    exact actual_typed_width_down O (typed_reduce_heads O xh le_rfl take) (by omega)
  · have yes : 0<originalThresholdCount m (y+1) := (original_threshold_prefix m hm (y+1) ⟨0,ht⟩).1 (by change _≤m ⟨0,ht⟩;dsimp only [H] at larger xh;omega)
    have protect := actual_rectangle_le_column (r:=r) n m hn hm (show x+(y+1)-1=D+1 by omega) rf yes
    change f+originalThresholdCount m (y+1)-1-r≤_ at protect
    change widthAt n m r D=f+g-1-r at span
    exact Or.inl (by omega)

theorem width_swap_on_original_row {s t:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (r j:ℕ) :
    widthAt m n r j=widthAt n m r j := by
  unfold widthAt offsetsAt
  rw [show rowCount t s r=rowCount s t r by simp only [rowCount,Nat.add_comm t s]]
  congr 1;apply Finset.filter_congr;intro k _;rw [diagonal_swap m n]

theorem even_total_top_typed {A B:Type u} [Finite A] [Finite B] (O:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y p:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hs:0<s) (ht:0<t) (hn:Antitone n) (hm:Antitone m)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r)
    (win:WinsHeight n m r (2*p) x y) (cap:∀z,Nat.card (C.neighborSet z)≤2*p)
    (heads:2*p+2≤n ⟨0,hs⟩+m ⟨0,ht⟩) (top:widthAt n m r (2*p+1)≤1) :
    ExactTypedWidth O x y (widthAt n m r (2*p)-Nat.card B/(min x y+1)) := by
  obtain ⟨px,py,eq,rf,bg,span⟩ := win
  by_cases even:x%2=0
  · exact even_split_top_red O C n m hs ht hn hm row ⟨px,py,eq,rf,bg,span⟩ even (by omega) cap heads top
  · have w : WinsHeight m n r (2*p) y x := ⟨py,px,by omega,bg,rf,by rw [width_swap_on_original_row n m,span,Nat.add_comm (originalThresholdCount n x)]⟩
    have take := even_split_top_red O C m n ht hs hm hn (swap_positive_forcing_row _ _ _ row) w (by omega) (by omega) cap (by omega)
      (by rw [width_swap_on_original_row n m];exact top)
    rw [width_swap_on_original_row n m,min_comm y x] at take
    exact exact_typed_width_swap O take

#print axioms even_split_top_red
#print axioms width_swap_on_original_row
#print axioms even_total_top_typed
end JSP452Audit.StarHost
