import BinaryComponentOptions
import ExactPathEvenSplit
import CapacitySplit
namespace JSP452Audit.StarHost
open SimpleGraph
/-- Components with fewer edges than vertices will supply continuously
splittable matching capacity. Isolated vertices are handled separately. -/
noncomputable def pathLike {X : Type*} (G : SimpleGraph X) (c : G.ConnectedComponent) : Prop :=
  c.toSimpleGraph.edgeSet.ncard < Nat.card c.supp
noncomputable def pathCapacity {X : Type*} [Finite X] (G : SimpleGraph X) : ℕ := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  exact ∑ c : G.ConnectedComponent, if pathLike G c then matchingEdges c.toSimpleGraph else 0
end JSP452Audit.StarHost