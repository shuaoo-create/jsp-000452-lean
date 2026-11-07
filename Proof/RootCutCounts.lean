import HallNeighborhoods
namespace JSP452Audit.StarHost

/-- Count all the simultaneously chosen representatives away from a root cut.
The representatives of components touched by the cut are excluded. -/
theorem away_image_count {C X : Type*} [Finite C] [Finite X] (F B : Set C)
    (sub : B⊆F) (label : C → X) (injects : Function.Injective label) (W : Set X)
    (hit : ∀c∈B,label c∉W) :
    ((label '' F) ∩ W).ncard+B.ncard≤F.ncard := by
  have kept : (label '' F) ∩ W ⊆ label '' (F \ B) := by
    rintro x ⟨⟨c,hc,rfl⟩,away⟩
    exact ⟨c,⟨hc,fun hb => hit c hb away⟩,rfl⟩
  have upper := Set.ncard_le_ncard kept
  rw [Set.ncard_image_of_injective _ injects] at upper
  have size := Set.ncard_sdiff_add_ncard_of_subset sub
  omega
#print axioms away_image_count
end JSP452Audit.StarHost
