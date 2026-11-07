import BothTenDegreeSourcesGiveOneLowDefectInterface
namespace JSP452Audit.StarHost.TenBlockPartition
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenBlockPartition G)
noncomputable abbrev capacity := matchingEdges (G.induce K.core)
noncomputable abbrev outsideRank := matchingEdges (G.induce K.rest)

theorem off_roots : K.core∪K.rest=K.rootsᶜ := by
  ext x
  constructor
  · rintro (c|r) a;exact Set.disjoint_left.mp K.rootsCore a c;exact Set.disjoint_left.mp K.rootsRest a r
  · intro out
    have mem : x∈K.roots∪K.core∪K.rest := K.cover.symm ▸ Set.mem_univ x
    rcases mem with (a|c)|r
    · exact (out a).elim
    · exact Or.inl c
    · exact Or.inr r

noncomputable def after_roots_iso : (G.induce K.core⊕g G.induce K.rest) ≃g G.induce K.rootsᶜ :=
  regionSumIso G _ _ _ K.off_roots K.coreRest K.apart

theorem erased_core_rank :
    matchingEdges (eraseInternal G K.core)=K.roots.ncard+matchingEdges (G.induce K.rest) := by
  let Z := eraseInternal G K.core
  have cover := K.off_roots
  have apart := K.coreRest
  have sep := K.apart
  let iso := regionSumIso Z K.rootsᶜ K.core K.rest cover apart (fun x hx y hy e => sep x hx y hy e.1)
  have ext : Z.induce K.rest=G.induce K.rest := by
    ext a b
    exact ⟨fun e => e.1,fun e => ⟨e,fun k => Set.disjoint_left.mp apart k.1 a.property⟩⟩
  have rank := (rank_eq_of_graph_iso iso).symm
  have empty : Z.induce K.core=⊥ := eraseInternal_induce_inside G K.core
  rw [matchingEdges_sumGraph,empty,ext,matchingEdges_bot,Nat.zero_add] at rank
  have upper := matching_rank_le_cut_add Z K.roots
  rw [rank] at upper
  have partition := K.rank
  change matchingEdges G=K.roots.ncard+matchingEdges (G.induce K.core)+matchingEdges (G.induce K.rest) at partition
  have lower := rank_of_two_edge_colours G Z (G \ Z) (by
    intro a b edge
    by_cases h : Z.Adj a b
    · exact Or.inl h
    · exact Or.inr ⟨edge,h⟩)
  change matchingEdges G≤matchingEdges Z+matchingEdges (G \ eraseInternal G K.core) at lower
  rw [rank_of_internal_edges] at lower
  change matchingEdges Z=K.roots.ncard+matchingEdges (G.induce K.rest)
  exact Nat.le_antisymm upper (by omega)



theorem edge_fees (cap:∀x,Nat.card (G.neighborSet x)≤10) :
    let a := K.roots.ncard
    let mu := K.capacity
    let C := G.induce K.core
    let O := G.induce K.rest
    let Z := eraseInternal G K.core
    let eA := (G.induce K.roots).edgeSet.ncard
    let beta := crossCount G K.roots K.rest
    let sigma := rootShortfall G K.roots 10
    G.edgeSet.ncard=Z.edgeSet.ncard+C.edgeSet.ncard ∧
    G.edgeSet.ncard+sigma+eA=O.edgeSet.ncard+C.edgeSet.ncard+10*a ∧
    2*C.edgeSet.ncard+K.epsilon=20*mu+10*K.eta+sigma+2*eA+beta ∧
    2*G.edgeSet.ncard+K.epsilon=O.edgeSet.ncard+Z.edgeSet.ncard+10*(a+2*mu)+10*K.eta+eA+beta ∧
    2*O.edgeSet.ncard+10*(2*mu+a+K.eta)≤2*G.edgeSet.ncard+K.epsilon := by
  intro a mu C O Z eA beta sigma
  have whole := erase_internal_edge_count G K.core
  have split : (C⊕g O).edgeSet.ncard=(G.induce K.rootsᶜ).edgeSet.ncard := Nat.card_congr K.after_roots_iso.mapEdgeSet
  rw [edge_ncard_sumGraph] at split
  have root := root_deletion_cost_with_slack G K.roots 10 (fun x _ => cap x)
  change G.edgeSet.ncard+sigma+eA=(G.induce K.rootsᶜ).edgeSet.ncard+10*a at root
  have coreHand := partition_handshake G K.core K.roots K.rest K.rootsCore.symm K.coreRest K.rootsRest
    (by rw [Set.union_comm K.core K.roots];exact K.cover)
  have no : crossCount G K.core K.rest=0 := crossCount_of_no_edges _ _ _ K.apart
  rw [no,Nat.add_zero,crossCount_swap G K.core K.roots] at coreHand
  change originalDegreeSum G K.core=2*C.edgeSet.ncard+crossCount G K.roots K.core at coreHand
  have rootHand := partition_handshake G K.roots K.core K.rest K.rootsCore K.rootsRest K.coreRest K.cover
  change originalDegreeSum G K.roots=2*eA+crossCount G K.roots K.core+beta at rootHand
  have bounded := degree_sum_le_cap G K.roots 10 (fun x _ => cap x)
  have rDef : originalDegreeSum G K.roots+sigma=10*a := by
    change originalDegreeSum G K.roots+(10*K.roots.ncard-originalDegreeSum G K.roots)=10*K.roots.ncard;omega
  have deg := K.degrees
  have ord := K.order
  change K.core.ncard=2*mu+a+K.eta at ord
  change G.edgeSet.ncard=Z.edgeSet.ncard+C.edgeSet.ncard at whole
  omega

#print axioms erased_core_rank
#print axioms edge_fees
end JSP452Audit.StarHost.TenBlockPartition
