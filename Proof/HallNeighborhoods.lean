import AllocationExposure
namespace JSP452Audit.StarHost
open SimpleGraph
def rootNeighbors {A C : Type*} (L : A → C → Prop) (T : Set C) : Set A := {a | ∃ c ∈ T, L a c}
def rootIncidence {X : Type*} (G : SimpleGraph X) (S : Set X) (a : S)
    (c : (G.induce Sᶜ).ConnectedComponent) : Prop := ∃ z : c.supp, G.Adj a.val z.val.val
theorem rootNeighbors_empty {A C : Type*} (L : A → C → Prop) :
    rootNeighbors L ∅=∅ := by ext; simp [rootNeighbors]
end JSP452Audit.StarHost