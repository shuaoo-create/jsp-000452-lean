import ActualRootCutBound
import BadPortHall

namespace JSP452Audit.StarHost
open SimpleGraph

/-- On a specific exposure-minimizing allocation, a relation on a subset of
the free full components may restrict root incidence further. The same real
partial assignment realizes both bounds whenever every component of B has a
root in that relation. -/
theorem bad_ports_selected {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S)
    (data : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
      PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (D : ℕ) (pos : 0<D) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (A : RootAllocation G S) (opt : (freeFull G S D A).ncard = minimumExposure G D)
    (B : Set (G.induce Sᶜ).ConnectedComponent) (inside : B ⊆ freeFull G S D A)
    (Inc : ↥B → ↥S → Prop) (refines : ∀ c a, Inc c a → rootIncidence G S a c.val)
    (touches : ∀ c, ∃ a, Inc c a) :
    ∃ (selected : Set ↥B) (assign : ↥selected ↪ ↥S),
      (∀ c, Inc c.val (assign c)) ∧
      B.ncard ≤ selected.ncard+(minimumExposure G D-deletionBudget G D) ∧
      ∀ h, B.ncard+h=minimumExposure G D → deletionBudget G D-h ≤ selected.ncard := by
  have limit (T : Set ↥S) :
      (rootNeighbors Inc T).ncard ≤ T.ncard+(minimumExposure G D-deletionBudget G D) := by
    have restrict : Subtype.val '' (rootNeighbors Inc T) ⊆ touchedFree G S D A T := by
      rintro _ ⟨c,⟨a,atRoot,related⟩,rfl⟩
      exact ⟨inside c.property,a,atRoot,refines c a related⟩
    have bound := Set.ncard_le_ncard restrict
    rw [Set.ncard_image_of_injective _ Subtype.val_injective] at bound
    exact bound.trans (optimal_root_cut_slack G S tight data D pos cap A opt T)
  obtain ⟨selected,assign,actual,count⟩ :=
    bad_port_partial_assignment Inc (minimumExposure G D-deletionBudget G D) limit touches
  rw [Nat.card_coe_set_eq] at count
  refine ⟨selected,assign,actual,count,?_⟩
  intro h balance
  have upper := deletionBudget_le_minimumExposure G D pos cap
  omega

#print axioms bad_ports_selected
end JSP452Audit.StarHost
