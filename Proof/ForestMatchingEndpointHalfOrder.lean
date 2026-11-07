import ForestEndpointDeletion
import RobustHalfOrderGap
import ActualEvenCutAxisInventory
namespace JSP452Audit.StarHost
open SimpleGraph

theorem endpoint_barrier_half_order {X : Type*} [Finite X] {s q d : ℕ}
    (G : SimpleGraph X) (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint G n q)
    (pos : 0<d) (hq : 0<q) (room : q≤matchingEdges G) (account : matchingEdges G+d+1=s+q)
    (S : Set X) (tight : IsTightBarrier G S)
    (crit : ∀c:(G.induce Sᶜ).ConnectedComponent,PerfectAfterEveryDeletion c.toSimpleGraph) :
    S.ncard+2*(d+∑i,(n i-1)/2)≤q := by
  classical
  let H := G.induce Sᶜ
  let _ := Fintype.ofFinite H.ConnectedComponent
  let b := S.ncard
  let k := q-1-b
  have small := tight_endpoint_barrier_lt G n pn endpt pos hq account S tight
  have split := tight_deletes_rank G S S tight (fun _ h => h)
  change matchingEdges G=b+matchingEdges H at split
  have sum : k+b+1=q := by dsimp [k,b];omega
  obtain ⟨U,card,charge⟩ := region_even_deletion_set H crit (k/2) (by omega)
  have survive : ∀W:Set X,W⊆Sᶜ → W.ncard≤k → (forest n).IsContained (G.induce (Sᶜ\W)) := by
    intro W outside size
    have apart : Disjoint S W := Set.disjoint_left.mpr (fun _ ins w => outside w ins)
    have num : (S∪W).ncard=b+W.ncard := Set.ncard_union_eq apart
    have copy := endpoint_survives_cover G n pn endpt (S∪W) (by omega)
    have eq : (S∪W)ᶜ=Sᶜ\W := by ext; simp [Set.mem_diff]
    rwa [eq] at copy
  obtain ⟨f⟩ := robust_core_subtype n G Sᶜ k survive U (by omega)
  have costs := critical_half_orders_off_cover H n U f crit
  rw [full_half_order_identity n pn,charge] at costs
  change b+2*(d+∑i,(n i-1)/2)≤q
  clear * - costs sum account split
  omega

theorem endpoint_forest_parity_cost {X : Type*} [Finite X] {s q d : ℕ}
    (G : SimpleGraph X) (n : Fin s→ℕ) (pn : ∀i,1≤n i) (endpt : ForestMatchingEndpoint G n q)
    (pos : 0<d) (hq : 0<q) (room : q≤matchingEdges G) (account : matchingEdges G+d+1=s+q) :
    2*(d+∑i,(n i-1)/2)≤q := by
  obtain ⟨S,tight,data⟩ := exists_critical_barrier G
  have bound := endpoint_barrier_half_order G n pn endpt pos hq room account S tight (fun c => (data c).2)
  omega

#print axioms endpoint_barrier_half_order
#print axioms endpoint_forest_parity_cost
end JSP452Audit.StarHost
