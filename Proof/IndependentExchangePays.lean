import IndependentLayers
import ReserveTruncation
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- An actual independent full-degree cut with enough simultaneous edge
repairs pays all top exposure. No assumption of factor-criticality is made. -/
theorem independent_exchange_pays (G : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (I : Set X) (ind : G.IsIndepSet I) (full : ∀x∈I,Nat.card (G.neighborSet x)=D)
    (m : ℕ) (size : I.ncard=minimumExposure G D+2*m)
    (enough : deletionBudget G D≤m) (rank : matchingEdges G≤matchingEdges (G.induce Iᶜ)+m)
    (clear : deletionBudget (G.induce Iᶜ) D = 0) :
    baseReserve (G.induce Iᶜ) D + minimumExposure G D ≤ baseReserve G D := by
  have eq : D-1+1=D := by omega
  have bal := independent_layers_account G I (D-1) ind (by simpa [eq] using full)
  dsimp only at bal
  rw [eq,clear] at bal
  omega
#print axioms independent_exchange_pays
end JSP452Audit.StarHost
