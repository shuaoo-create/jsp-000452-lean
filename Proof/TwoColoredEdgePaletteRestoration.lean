import ActualCoveringColorsOnPortEdges
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Width after distributing the missing original edges between two colors,
with explicit damage bounds for each color of every exterior coloring. -/
theorem two_palette_typed_restoration {X : Type*} [Finite X] (G Y P Q : SimpleGraph X)
    (old : Y≤G) (redSub : P≤G) (cover : G≤(Y⊔P)⊔Q) {s t r a b u v : ℕ}
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (aLive : u<originalThresholdCount n a) (bLive : v<originalThresholdCount m b)
    (red : ∀A : SimpleGraph X,A≤Y → ∀k,∀f : (forest (fun _ : Fin k => a)).Copy (A⊔P),
      (touchedStars A P (fun _ : Fin k => a) f).ncard≤u)
    (blue : ∀A : SimpleGraph X,A≤Y → ∀k,∀f : (forest (fun _ : Fin k => b)).Copy (A⊔Q),
      (touchedStars A Q (fun _ : Fin k => b) f).ncard≤v)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ExactTypedWidth Y a b (originalThresholdCount n a+originalThresholdCount m b-1-r-u-v) := by
  let f := originalThresholdCount n a
  let g := originalThresholdCount m b
  change ExactTypedWidth Y a b (f+g-1-r-u-v)
  change u<f at aLive
  change v<g at bLive
  by_cases dead : f+g-1-r≤u+v
  · exact Or.inl (by omega)
  let i := min r (f-u-1)
  let j := r-i
  have idx : i+j=r := by dsimp [i,j];omega
  have fitR : i+u<f := by dsimp [i];omega
  have fitB : j+v<g := by dsimp [i,j];omega
  have orig := uniform_rectangle_at G n m hn hm idx (show i<f by omega) (show j<g by omega) row
  refine Or.inr ⟨f-i-u,g-j-v,by omega,by omega,by omega,?_⟩
  intro A sub
  rcases restored_pair_outcome G Y P Q old redSub cover _ _ orig A sub with cr|cb
  · obtain ⟨copy⟩ := cr
    exact Or.inl (trim_touched_uniform_copy A P (f-i) a u copy (red A sub _ copy))
  · obtain ⟨copy⟩ := cb
    exact Or.inr (trim_touched_uniform_copy (Y \ A) Q (g-j) b v copy (blue _ sdiff_le _ copy))

#print axioms two_palette_typed_restoration
end JSP452Audit.StarHost
