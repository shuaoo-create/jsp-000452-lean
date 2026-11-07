import RootAllocation
import RootPlanCounts
import ExposeRestrict

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Identify the actual exposed full-degree vertices as original labels of
unassigned all-full components. Assigned components need no degree assumption. -/
theorem exposedFull_eq_label_image (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) (M : G.Subgraph)
    (holes : M.vertsᶜ = freeHoleLabels G S A.place pick)
    (exactDegree : ∀ c, c ∉ Set.range A.place →
      (Nat.card (G.neighborSet (pick c).val.val) = D ↔ allFullComponent G S D c)) :
    exposedFull G M D = (fun c => (pick c).val.val) '' freeFull G S D A := by
  ext v
  constructor
  · rintro ⟨miss,degree⟩
    have free : v ∈ freeHoleLabels G S A.place pick := holes ▸ miss
    obtain ⟨c,unused,rfl⟩ := free
    exact ⟨c,⟨unused,(exactDegree c unused).mp degree⟩,rfl⟩
  · rintro ⟨c,⟨unused,full⟩,rfl⟩
    have free : (pick c).val.val ∈ freeHoleLabels G S A.place pick := ⟨c,unused,rfl⟩
    exact ⟨show (pick c).val.val ∈ M.vertsᶜ from holes.symm ▸ free,(exactDegree c unused).mpr full⟩

theorem exposed_eq_freeFull (G : SimpleGraph X) (S : Set X) (D : ℕ) (A : RootAllocation G S)
    (pick : ∀ c : (G.induce Sᶜ).ConnectedComponent, c.supp) (M : G.Subgraph)
    (holes : M.vertsᶜ = freeHoleLabels G S A.place pick)
    (exactDegree : ∀ c, c ∉ Set.range A.place →
      (Nat.card (G.neighborSet (pick c).val.val) = D ↔ allFullComponent G S D c)) :
    (exposedFull G M D).ncard = (freeFull G S D A).ncard := by
  rw [exposedFull_eq_label_image G S D A pick M holes exactDegree,
    Set.ncard_image_of_injective _ (picked_original_injective G S pick)]

#print axioms exposedFull_eq_label_image
#print axioms exposed_eq_freeFull
end JSP452Audit.StarHost
