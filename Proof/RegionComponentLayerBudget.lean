import ProtectedBudgetSplit
import CoreComponentSum

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- Deletion at a fixed height adds over every component of a finite graph. -/
theorem deletionBudget_component_total {X : Type*} [Finite X] (G : SimpleGraph X)
    [Fintype G.ConnectedComponent] (j : ℕ) :
    deletionBudget G j = ∑ c : G.ConnectedComponent, deletionBudget c.toSimpleGraph j := by
  classical
  let U (T : Finset G.ConnectedComponent) : Set X := {x | G.connectedComponentMk x ∈ T}
  have part (T : Finset G.ConnectedComponent) :
      deletionBudget (G.induce (U T)) j = ∑ c ∈ T, deletionBudget c.toSimpleGraph j := by
    induction T using Finset.induction_on with
    | empty =>
      let H := G.induce (U ∅)
      let _ : IsEmpty ↥(U ∅) := ⟨fun x => Finset.notMem_empty _ x.property⟩
      have witness : admits_matching_remainder (H.induce (∅ : Set ↥(U ∅))ᶜ) j :=
        ⟨⊥,fun x _ => isEmptyElim x.val,fun x => isEmptyElim x.val⟩
      have upper := deletionBudget_le_of_witness H j ∅ witness
      simpa only [Finset.sum_empty,Set.ncard_empty,Nat.le_zero] using upper
    | @insert c T fresh ih =>
      have cover : c.supp ∪ U T = U (insert c T) := by ext x; exact Finset.mem_insert.symm
      have apart : Disjoint c.supp (U T) := Set.disjoint_left.mpr fun _ hx ht =>
        fresh ((show G.connectedComponentMk _ = c from hx) ▸ ht)
      have sep : ∀ x∈c.supp, ∀ y∈U T, ¬G.Adj x y := fun _ hx _ hy edge =>
        Set.disjoint_left.mp apart ((c.mem_supp_congr_adj edge).mp hx) hy
      rw [deletionBudget_split_regions G _ _ _ j cover apart sep,ih,Finset.sum_insert fresh]
      rfl
  have result := part Finset.univ
  have all : U Finset.univ = Set.univ := by ext x; simp [U]
  rw [all,deletionBudget_iso (induceUnivIso G) j] at result
  exact result

/-- The original vertex-label core has exactly the sum of the local budgets on
the selected residual components, with no contribution from any other component. -/
theorem region_component_layer_budget {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] (j : ℕ) :
    deletionBudget (G.induce (regionCore G S T)) j = ∑ c : T, deletionBudget c.val.toSimpleGraph j := by
  classical
  let H := G.induce (regionCore G S T)
  let _ := Fintype.ofFinite H.ConnectedComponent
  calc
    deletionBudget H j = ∑ c : H.ConnectedComponent, deletionBudget c.toSimpleGraph j :=
      deletionBudget_component_total H j
    _ = ∑ c : T, deletionBudget c.val.toSimpleGraph j :=
      Fintype.sum_equiv (coreComponentEquiv G S T) _ _ (fun c => deletionBudget_iso (coreComponentIso G S T c) j)

#print axioms deletionBudget_component_total
#print axioms region_component_layer_budget
end JSP452Audit.StarHost
