import GoodPortLayerDrop
import GoodPortClassification
import OddRegionPort
import IndependentLayers
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
/-- One actual full vertex suffices to pay the penultimate layer of a
good split piece; its neighbors all lose one and the deletion has a perfect matching. -/
theorem good_split_penultimate_cost (Q : SimpleGraph X) (D : ℕ) (large : 2≤D)
    (cap : ∀x,Nat.card (Q.neighborSet x)≤D) (crit : PerfectAfterEveryDeletion Q)
    (good : internallyGood Q D) (split : GoodPortSplit Q D) :
    deletionBudget Q (D-1)≤1 := by
  have room := split.room
  obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero (by omega : (portFull Q D).ncard≠0)
  have cl : Q.IsClique (portFull Q D) := fun x hx y _ diff => (split.join x y).mpr ⟨diff,Or.inl hx⟩
  have zero := (good_port_layer_drop Q D large cap crit good cl v hv).2
  have bound := deletion_le_after_cut_add Q {v} (D-1)
  change deletionBudget (Q.induce ({v}:Set X)ᶜ) (D-1)=0 at zero
  rwa [Set.ncard_singleton,zero,add_zero] at bound

#print axioms good_split_penultimate_cost
end JSP452Audit.StarHost
