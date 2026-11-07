import IndependentLayers
import ReserveTruncation
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- The one below-top saving pays exactly the remaining good-component
deficiency, allowing extra independent labels beyond the original exposure. -/
theorem independent_cut_one_layer_pays (G : SimpleGraph X) (D : ℕ) (large : 2≤D)
    (I : Set X) (ind : G.IsIndepSet I) (full : ∀x∈I,Nat.card (G.neighborSet x)=D)
    (t b h : ℕ) (size : I.ncard=minimumExposure G D+t+b)
    (rank : matchingEdges G≤matchingEdges (G.induce Iᶜ)+t)
    (enough : deletionBudget G D≤b+h)
    (saving : h≤savedAt G I (D-1)) :
    baseReserve (G.induce Iᶜ) D + minimumExposure G D ≤ baseReserve G D := by
  have top : D-1+1=D := by omega
  have prev : D-2+1=D-1 := by omega
  have bal := independent_layers_account G I (D-1) ind (by simpa [top] using full)
  dsimp only at bal
  rw [top] at bal
  have term : savedAt G I ((D-2)+1)≤∑ j∈Finset.range (D-1),savedAt G I (j+1) :=
    Finset.single_le_sum (f:=fun j => savedAt G I (j+1)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr (by omega))
  rw [prev] at term
  omega
#print axioms independent_cut_one_layer_pays
end JSP452Audit.StarHost
