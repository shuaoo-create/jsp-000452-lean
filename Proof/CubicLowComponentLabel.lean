import StrictCubicBinaryAxis
import RobustUnusedMass
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An odd deletion-critical component in a subcubic graph must contain a
vertex of original degree at most two. Its external cut has no edges. -/
theorem cubic_component_low_label (H : SimpleGraph X) (cap : ∀v,Nat.card (H.neighborSet v)≤3)
    (c:H.ConnectedComponent) (crit : PerfectAfterEveryDeletion c.toSimpleGraph) :
    ∃x∈c.supp,Nat.card (H.neighborSet x)≤2 := by
  by_contra! none
  have full (v:X) (hv:v∈c.supp) : Nat.card (H.neighborSet v)=3 := by have := none v hv;have := cap v;omega
  have capSum := degree_sum_full H c.supp 3 full
  have hand := partition_handshake H c.supp c.suppᶜ ∅ disjoint_compl_right (by simp) (by simp) (by simp)
  have outer := crossCount_of_no_edges H c.supp c.suppᶜ (fun x hx y hy edge => hy ((c.mem_supp_congr_adj edge).mp hx))
  have nil := crossCount_of_no_edges H c.supp ∅ (fun _ _ _ h _ => h.elim)
  rw [outer,nil] at hand
  have size := factorCritical_order_rank c.toSimpleGraph crit c.nonempty_supp.to_subtype.some
  change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at size
  rw [Nat.card_coe_set_eq] at size
  omega

/-- A region closed under adjacency contains the full component of any of
its vertices. -/
theorem cubic_closed_component (H : SimpleGraph X) (Z:Set X) (z:X) (hz:z∈Z)
    (closed : ∀v∈Z,∀w,H.Adj v w → w∈Z) : (H.connectedComponentMk z).supp⊆Z := by
  intro w hw
  have reach := (H.connectedComponentMk z).reachable_of_mem_supp (show z∈(H.connectedComponentMk z).supp from rfl) hw
  have path := (H.reachable_iff_reflTransGen z w).mp reach
  clear hw reach
  induction path with
  | refl => exact hz
  | tail old edge ih => exact closed _ ih _ edge

#print axioms cubic_component_low_label
#print axioms cubic_closed_component
end JSP452Audit.StarHost
