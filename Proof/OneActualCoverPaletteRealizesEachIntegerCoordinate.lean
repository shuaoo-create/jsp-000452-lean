import IntegerPointCoverBoundAndShrinkingAnActualTypedWitness
namespace JSP452Audit.StarHost
open SimpleGraph
theorem typed_cover_red_coordinate {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (fits:(x+1)*originalThresholdCount n x≤Nat.card Y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth O x y (originalThresholdCount n x+originalThresholdCount m y-1-r-(Nat.card Y-x*originalThresholdCount n x)) := by
  let f := originalThresholdCount n x
  let g := originalThresholdCount m y
  let N := Nat.card Y
  let v := N-(x+1)*f+1
  change 0<f at red
  change 0<g at blue
  change (x+1)*f≤N at fits
  have expand : (x+1)*f=x*f+f := by rw [Nat.add_mul,one_mul]
  have fv : f-1+v=N-x*f := by dsimp [v];omega
  have modest : v≤N := by dsimp [v];omega
  change ExactTypedWidth O x y (f+g-1-r-(N-x*f))
  by_cases paid : f+g-1-r≤N-x*f
  · exact Or.inl (by omega)
  have live : v<g := by omega
  obtain ⟨S,_,card⟩ := Set.exists_subset_card_eq (s:=(Set.univ:Set Y)) (n:=v) (by simpa [N] using modest)
  obtain ⟨P,sub,a,b⟩ := split_cover_palette C S x y rx byh
  have sum := Set.ncard_add_ncard_compl S
  change S.ncard+Sᶜ.ncard=N at sum
  have small : Sᶜ.ncard/(x+1)≤f-1 := by
    have short : Sᶜ.ncard<f*(x+1) := by dsimp [v] at card;rw [Nat.mul_comm f (x+1)];omega
    have := (Nat.div_lt_iff_lt_mul (by omega : 0<x+1)).mpr short
    omega
  have acap : UniformPackCap P x (f-1) := fun k copy => (a k copy).trans small
  rw [card] at b
  have price := palette_retains_typed_rectangle O C P sub n m hn hm rx byh acap b (by change f-1<f;omega) live row
  change ExactTypedWidth O x y (f+g-1-r-(f-1)-v) at price
  rwa [show f+g-1-r-(f-1)-v=f+g-1-r-(N-x*f) by omega] at price

theorem typed_cover_blue_coordinate {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (fits:(y+1)*originalThresholdCount m y≤Nat.card Y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth O x y (originalThresholdCount n x+originalThresholdCount m y-1-r-(Nat.card Y-y*originalThresholdCount m y)) := by
  have swapped := typed_cover_red_coordinate O C m n hm hn byh rx blue red fits (swap_positive_forcing_row (O⊕g C) _ _ row)
  rw [Nat.add_comm (originalThresholdCount m y)] at swapped
  exact exact_typed_width_swap O swapped


#print axioms typed_cover_red_coordinate
#print axioms typed_cover_blue_coordinate
end JSP452Audit.StarHost
