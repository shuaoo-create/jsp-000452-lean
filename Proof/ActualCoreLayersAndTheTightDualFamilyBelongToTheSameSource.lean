import SeedTheActualOrdinaryFullRegionAndKeepTheOutsideAssignments
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D:ℕ}

structure ScaledPortPlan (K:DegreeRegion G D) (k c:ℕ) where
  original : RootAllocation G K.barrier
  originalInside : ∀a:K.barrier,original.place a∈K.pieces ↔ a.val∈K.roots
  originalMisses : K.pieces\Set.range original.place=freeFull G K.barrier D original
  matching : (portIncidenceGraph (slotIncidence K.actualLink (rootScale G D k c) k)).Subgraph
  proper : matching.IsMatching
  layers : ActualAssignmentLayers proper K.roots
  family : Set K.pieces
  tight : k*family.ncard=k*(regionRoots G K.barrier (Subtype.val '' family)).ncard+
    c*rootShortfall G (regionRoots G K.barrier (Subtype.val '' family)) D+
      ∑t:Fin k,((layers.assigned t)ᶜ:Set K.pieces).ncard
  assignedRoots : ∃f:↥(regionRoots G K.barrier (Subtype.val '' family)) ↪ ↥family,
    ∀r,K.actualLink r.val (f r).val

theorem scaled_port_plan_exists (K:DegreeRegion G D) (k c:ℕ) (live:0<k) (cap:∀x,Nat.card (G.neighborSet x)≤D) :
    Nonempty (ScaledPortPlan K k c) := by
  let w := rootScale G D k c
  have base (x:X) : k≤w x := Nat.le_add_right _ _
  obtain ⟨P,outside,free,seed,links⟩ := K.original_roots_seed_the_scaled_problem
  obtain ⟨M,hm,B,miss,_,_⟩ := exists_layered_scaled_assignment K.actualLink w k live K.roots (fun x _ => base x) seed links
  obtain ⟨_,J,sub,att,_⟩ := actual_scaled_hall_witness K.actualLink w k live Set.univ
  obtain ⟨f,ok⟩ := tight_slot_actual_root_matching K.actualLink w k live base Set.univ J sub att
  have labels := K.actual_link_neighbors J
  rw [labels] at att
  have matchRoots : ∃g:↥(regionRoots G K.barrier (Subtype.val '' J)) ↪ ↥J,∀r,K.actualLink r.val (g r).val := by
    rw [←labels];exact ⟨f,ok⟩
  rw [←miss] at att
  have fee := root_slots_count_original_deficit G D k c (regionRoots G K.barrier (Subtype.val '' J)) cap
  change rootSlotCount (regionRoots G K.barrier (Subtype.val '' J)) w=_ at fee
  rw [fee] at att
  exact ⟨⟨P,outside,free,M,hm,B,J,att,matchRoots⟩⟩

theorem ScaledPortPlan.true_rank_and_degree {K:DegreeRegion G D} {k c:ℕ} (P:ScaledPortPlan K k c) :
    let J := Subtype.val '' P.family
    let roots := regionRoots G K.barrier J
    let core := regionCore G K.barrier J
    let rest := regionRest G K.barrier J
    (∀x∈core,Nat.card (G.neighborSet x)=D) ∧ (∀x∈core,∀y∈rest,¬G.Adj x y) ∧
    core.ncard=2*matchingEdges (G.induce core)+P.family.ncard ∧
    matchingEdges G=roots.ncard+matchingEdges (G.induce core)+matchingEdges (G.induce rest) := by
  intro J roots core rest
  have sub : J⊆K.pieces := by rintro _ ⟨Q,_,rfl⟩;exact Q.property
  have full (x:X) (hx:x∈core) := regionCore_full_degree G K.barrier J D (fun Q mem => K.full (sub mem)) hx
  have ord := core_order_matching G K.barrier K.tight J (fun Q _ => (K.critical Q).1)
  have count : J.ncard=P.family.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  rw [count] at ord
  exact ⟨full,fun _ a _ b => no_edge_core_rest G K.barrier J a b,ord,region_rank_partition G K.barrier K.tight J⟩

#print axioms scaled_port_plan_exists
#print axioms ScaledPortPlan.true_rank_and_degree
end JSP452Audit.StarHost
