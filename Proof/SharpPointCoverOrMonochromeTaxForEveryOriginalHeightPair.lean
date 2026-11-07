import OneActualCoverPaletteRealizesEachIntegerCoordinate
namespace JSP452Audit.StarHost
open SimpleGraph

theorem genuine_uniform_pack_cap {B:Type*} [Finite B] (C:SimpleGraph B) (x:ℕ) (pos:0<x) :
    UniformPackCap C x (min (matchingEdges C) (Nat.card B/(x+1))) := by
  intro l copy
  have size := uniform_pack_order_cap C x pos Set.univ (fun _ _ _ => Set.mem_univ _) l copy
  rw [Set.ncard_univ] at size
  exact le_min ((uniform_pack_rank_cap C x pos) l copy) size

theorem sharp_summand_coordinate {A B:Type*} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (px:0<x) (py:0<y) (rf:0<originalThresholdCount n x) (bg:0<originalThresholdCount m y)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r) :
    let L := originalThresholdCount n x+originalThresholdCount m y-1-r
    ExactTypedWidth Y x y (L-pointCoordinateTax (matchingEdges C) (Nat.card B) r x y) := by
  intro L
  let N := Nat.card B
  let Z := matchingEdges C
  let a := min Z (N/(x+1))
  let b := min Z (N/(y+1))
  let J := pointCoordinateTax Z N r x y
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  have aJ : a≤J := (Nat.le_max_left _ b).trans (Nat.le_max_left _ _)
  have bJ : b≤J := (Nat.le_max_right a _).trans (Nat.le_max_left _ _)
  have cJ : coveredCoordinateTax N r x y≤J := Nat.le_max_right _ _
  change ExactTypedWidth Y x y (L-J)
  by_cases red:a<f
  · have take := palette_retains_typed_rectangle Y C C le_rfl n m hn hm px py (genuine_uniform_pack_cap C x px)
      (by rw [sdiff_self];exact uniform_pack_bot_cap y py) red bg row
    change ExactTypedWidth Y x y (L-a-0) at take
    exact actual_typed_width_down Y take (by omega)
  by_cases blue:b<g
  · have take := palette_retains_typed_rectangle Y C C le_rfl m n hm hn py px (genuine_uniform_pack_cap C y py)
      (by rw [sdiff_self];exact uniform_pack_bot_cap x px) blue rf (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m y)] at take
    change ExactTypedWidth Y y x (L-b-0) at take
    exact actual_typed_width_down Y (exact_typed_width_swap _ take) (by omega)
  have fx : f≤N/(x+1) := (Nat.le_of_not_gt red).trans (Nat.min_le_right _ _)
  have gy : g≤N/(y+1) := (Nat.le_of_not_gt blue).trans (Nat.min_le_right _ _)
  have fitsR : (x+1)*f≤N := (Nat.mul_comm f (x+1)) ▸ ((Nat.le_div_iff_mul_le (by omega)).mp fx)
  have fitsB : (y+1)*g≤N := (Nat.mul_comm g (y+1)) ▸ ((Nat.le_div_iff_mul_le (by omega)).mp gy)
  rcases cover_integer_alternative N r x y f g px py with free|rc|bc
  · change L≤_ at free;exact Or.inl (by omega)
  · have take := typed_cover_red_coordinate Y C n m hn hm px py rf bg fitsR row
    change ExactTypedWidth Y x y (L-(N-x*f)) at take
    exact actual_typed_width_down Y take (by omega)
  · have take := typed_cover_blue_coordinate Y C n m hn hm px py rf bg fitsB row
    change ExactTypedWidth Y x y (L-(N-y*g)) at take
    exact actual_typed_width_down Y take (by omega)

theorem unit_summand_coordinate {A B:Type*} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (len:matchingEdges C<min s t)
    (px:0<x) (py:0<y) (rf:0<originalThresholdCount n x) (bg:0<originalThresholdCount m y)
    (unit:x=1 ∨ y=1) (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth Y x y (originalThresholdCount n x+originalThresholdCount m y-1-r-matchingEdges C) := by
  rcases unit with rfl|rfl
  · have live : matchingEdges C<originalThresholdCount n 1 := (original_threshold_one n pn).symm ▸ (lt_min_iff.mp len).1
    have take := palette_retains_typed_rectangle Y C C le_rfl n m hn hm px py (uniform_pack_rank_cap C 1 px)
      (by rw [sdiff_self];exact uniform_pack_bot_cap y py) live bg row
    simpa only [Nat.sub_zero] using take
  · have live : matchingEdges C<originalThresholdCount m 1 := (original_threshold_one m pm).symm ▸ (lt_min_iff.mp len).2
    have take := palette_retains_typed_rectangle Y C C le_rfl m n hm hn py px (uniform_pack_rank_cap C 1 py)
      (by rw [sdiff_self];exact uniform_pack_bot_cap x px) live rf (swap_positive_forcing_row _ _ _ row)
    rw [Nat.add_comm (originalThresholdCount m 1),Nat.sub_zero] at take
    exact exact_typed_width_swap _ take

#print axioms genuine_uniform_pack_cap
#print axioms sharp_summand_coordinate
#print axioms unit_summand_coordinate
end JSP452Audit.StarHost
