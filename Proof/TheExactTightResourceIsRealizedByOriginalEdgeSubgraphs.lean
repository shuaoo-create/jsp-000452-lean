import ActualLayerEdgesAndTheSingleUncoveredFullVertexOfEachFreeCore
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D}

structure PortGraphLayers (P:ScaledPortPlan K k c) where
  graph : Fin k→SimpleGraph X
  missing : Fin k→Set X
  sub : ∀t,graph t≤G
  fullyExposed : ∀t x,x∈missing t → Nat.card (G.neighborSet x)=D
  count : ∀t,(missing t).ncard=((P.layers.assigned t)ᶜ:Set K.pieces).ncard
  full : ∀t x,Nat.card (G.neighborSet x)=D →
    (x∈missing t → Nat.card ((graph t).neighborSet x)=0) ∧
    (x∉missing t → Nat.card ((graph t).neighborSet x)=1)
  budget : ∀x,(∑t:Fin k,Nat.card ((graph t).neighborSet x))≤k+c*(D-Nat.card (G.neighborSet x))

theorem ScaledPortPlan.graph_layers (P:ScaledPortPlan K k c) : Nonempty (PortGraphLayers P) := by
  classical
  choose H U sub holes count roots rest full using P.actual_layer_edge_subgraph
  refine ⟨⟨H,U,sub,fun t x m => (holes t x m).2,count,full,?_⟩⟩
  intro x
  by_cases root:x∈K.barrier
  · simp_rw [roots _ x root];exact P.aggregate_root_degree x root
  · have upper := Finset.sum_le_sum (s:=Finset.univ) (fun t _ => rest t x root)
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id,Nat.mul_one] at upper
    exact upper.trans (Nat.le_add_right _ _)

theorem PortGraphLayers.true_total_misses {P:ScaledPortPlan K k c} (E:PortGraphLayers P) :
    let A := regionRoots G K.barrier (Subtype.val '' P.family)
    k*P.family.ncard=k*A.ncard+c*rootShortfall G A D+∑t:Fin k,(E.missing t).ncard := by
  intro A
  simp_rw [E.count];exact P.tight

#print axioms ScaledPortPlan.graph_layers
#print axioms PortGraphLayers.true_total_misses
end JSP452Audit.StarHost
