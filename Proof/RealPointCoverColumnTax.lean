import MonochromeAndCoveredPackCaps
namespace JSP452Audit.StarHost
open SimpleGraph

theorem point_cover_red_tax {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (fits:(x+1)*originalThresholdCount n x≤Nat.card Y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+(Nat.card Y-x*originalThresholdCount n x) := by
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
  change f+g-1-r≤uniformEnvelope O (x+y-1)+(N-x*f)
  by_cases paid : f+g-1-r≤N-x*f
  · omega
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
  have price := palette_rectangle_tax O C P sub n m hn hm rx byh acap b (by change f-1<f;omega) live row
  change f+g-1-r≤uniformEnvelope O (x+y-1)+(f-1)+v at price
  omega

theorem point_cover_blue_tax {X Y:Type*} [Finite X] [Finite Y] (O:SimpleGraph X) (C:SimpleGraph Y)
    {s t r x y:ℕ} (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (rx:0<x) (byh:0<y)
    (red:0<originalThresholdCount n x) (blue:0<originalThresholdCount m y)
    (fits:(y+1)*originalThresholdCount m y≤Nat.card Y)
    (row:ForcingRow (O⊕g C) s t (padDemand n) (padDemand m) r) :
    originalThresholdCount n x+originalThresholdCount m y-1-r≤uniformEnvelope O (x+y-1)+(Nat.card Y-y*originalThresholdCount m y) := by
  have swapped := point_cover_red_tax O C m n hm hn byh rx blue red fits (swap_positive_forcing_row (O⊕g C) _ _ row)
  rwa [Nat.add_comm (originalThresholdCount m y),Nat.add_comm y x] at swapped

#print axioms point_cover_red_tax
#print axioms point_cover_blue_tax
end JSP452Audit.StarHost
