import DoubleEmbeddedShortHeadExclusion
import DegreeSplitEnvelope
import InterpolateRegular
import HighStarCover
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An even/even bounded edge split at full total degree, on every original
finite host. The zero and full factors of the regular completion interpolate
without requiring a perfect matching. -/
theorem even_even_degree_split (G : SimpleGraph X) (u v : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*(u+v)) :
    ∃R:SimpleGraph X,R≤G ∧ ∀x,Nat.card (R.neighborSet x)≤2*u ∧
      Nat.card ((G \ R).neighborSet x)≤2*v := by
  let D := 2*(u+v)
  let H := regularEnvelope G D
  have bottom : HasFactor H 0 := ⟨⊥,bot_le,by intro x;simp⟩
  have full : HasFactor H (0+2*(u+v)) := ⟨H,le_rfl,fun x => by
    simpa only [Nat.zero_add] using regularEnvelope_degree G D cap x.1 x.2⟩
  obtain ⟨F,sub,reg⟩ := factor_interpolation H 0 u (u+v) (by omega) bottom full
  exact degreeSplit_of_envelopeFactor G D cap (2*u) (2*v) (by dsimp [D];omega) F sub
    (fun x => by simpa only [Nat.zero_add] using reg x)

/-- An attaining corner cannot require an odd positive star in each color at
the degree-sum threshold, since a split with even caps avoids both stars. -/
theorem no_odd_odd_star_corner (G : SimpleGraph X) (u v : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤2*(u+v))
    (forces : Forces G (oneStar (2*u+1)) (oneStar (2*v+1))) : False := by
  obtain ⟨R,sub,bound⟩ := even_even_degree_split G u v cap
  rcases forces R sub with reds|blues
  · obtain ⟨red⟩ := reds
    have degree := star_copy_center_degree R red
    have upper := (bound (red (center (fun _ : Fin 1 => 2*u+1) 0))).1
    omega
  · obtain ⟨blue⟩ := blues
    have degree := star_copy_center_degree (G \ R) blue
    have upper := (bound (blue (center (fun _ : Fin 1 => 2*v+1) 0))).2
    omega

#print axioms even_even_degree_split
#print axioms no_odd_odd_star_corner
end JSP452Audit.StarHost
