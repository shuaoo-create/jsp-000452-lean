import ComponentBudget
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Preserve the old vertex label when converting the library's deletion
    of the top subgraph to the induced graph outside a cut. -/
def topDeleteIso {X : Type*} (G : SimpleGraph X) (S : Set X) :
    ((⊤ : G.Subgraph).deleteVerts S).coe ≃g G.induce Sᶜ where
  toFun x := ⟨x.val,x.property.2⟩
  invFun y := ⟨y.val,Set.mem_univ _,y.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_rel_iff' := by
    intro x y
    change G.Adj x.val y.val ↔ _
    constructor
    · intro h
      exact ⟨x.property,y.property,h⟩
    · intro h
      exact h.2.2

theorem tutte_violator_induce {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X) :
    G.IsTutteViolator S ↔ S.ncard < (G.induce Sᶜ).oddComponents.ncard := by
  unfold SimpleGraph.IsTutteViolator
  rw [odd_ncard_iso (topDeleteIso G S)]

/-- In the presence of a remaining universal vertex the residual graph has at
    most one odd component, even when it is a singleton. -/
theorem odd_le_one_of_universal {Y : Type*} [Finite Y] (H : SimpleGraph Y)
    (u : Y) (hu : ∀ w, w ≠ u → H.Adj w u) : H.oddComponents.ncard ≤ 1 := by
  have eq (x : Y) : H.connectedComponentMk x = H.connectedComponentMk u := by
    by_cases h : x = u
    · rw [h]
    · exact SimpleGraph.ConnectedComponent.eq.mpr (hu x h).reachable
  apply (Set.ncard_le_one (s := H.oddComponents) (Set.toFinite _)).mpr
  intro c _ d _
  exact SimpleGraph.ConnectedComponent.ind₂ (fun x y => (eq x).trans (eq y).symm) c d

#print axioms tutte_violator_induce
#print axioms odd_le_one_of_universal
end JSP452Audit.StarHost
