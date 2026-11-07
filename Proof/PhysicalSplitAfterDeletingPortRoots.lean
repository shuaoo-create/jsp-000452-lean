import TwoNineDegreePortBlocks
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (R:NinePortRegion G)

theorem separated_after_roots : Nonempty ((G.induce R.chosen⊕g G.induce R.outside) ≃g G.induce R.rootsᶜ) := by
  have cover : R.chosen∪R.outside=R.rootsᶜ := by
    ext x
    constructor
    · rintro (h|h);exact fun a => Set.disjoint_left.mp R.chosen_away a h;exact fun a => h (Or.inl a)
    · intro h;by_cases inside:x∈R.chosen;exact Or.inl inside;exact Or.inr (fun mem => mem.elim h inside)
  have apart : Disjoint R.chosen R.outside := disjoint_compl_right.mono_left Set.subset_union_right
  have sep (x) (hx:x∈R.chosen) (y) (hy:y∈R.outside) (edge:G.Adj x y) : False := by
    rcases hx with in0|in1
    · rcases R.box_separation 0 in0 edge with old|root
      · exact hy (Or.inr (Or.inl old))
      · exact hy (Or.inl ⟨0,root.symm⟩)
    · rcases R.box_separation 1 in1 edge with old|root
      · exact hy (Or.inr (Or.inr old))
      · exact hy (Or.inl ⟨1,root.symm⟩)
  exact ⟨regionSumIso G R.rootsᶜ R.chosen R.outside cover apart sep⟩

theorem box_edge_count (cap:∀x,Nat.card (G.neighborSet x)≤9) (i:Fin 2) :
    (G.induce (R.box i)).edgeSet.ncard=9*R.capacity i+4 := by
  let U := R.box i
  let c := (R.select i).val
  have one := (R.select i).property
  have full (x) (hx:x∈U) := uniform_tight_piece_full G 3 6 cap R.K.S R.K.T c.val c.property x hx
  have boundary := actual_cut_piece_boundary_to_roots G R.K.S R.K.T R.K.apart c.val
  change crossCount G U Uᶜ=R.K.sPorts c+R.K.tPorts c at boundary
  change c∈R.K.onePortBlocks at one
  rw [one.1,one.2,Nat.add_zero] at boundary
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  rw [degree_sum_full G U 9 full,boundary] at hand
  have order := (R.inner i).1
  change U.ncard=2*R.capacity i+1 at order
  change (G.induce U).edgeSet.ncard=9*R.capacity i+4
  omega

theorem region_rank_edges (cap:∀x,Nat.card (G.neighborSet x)≤9) :
    matchingEdges (G.induce R.chosen)=R.totalCapacity ∧
    (G.induce R.chosen).edgeSet.ncard=9*R.totalCapacity+8 ∧
    matchingEdges (G.induce R.rootsᶜ)=R.totalCapacity+R.outsideRank ∧
    (G.induce R.rootsᶜ).edgeSet.ncard=9*R.totalCapacity+8+(G.induce R.outside).edgeSet.ncard := by
  obtain ⟨_,⟨e⟩⟩ := R.chosen_structure
  obtain ⟨h⟩ := R.separated_after_roots
  have q := rank_eq_of_graph_iso e
  have edgeQ : ((G.induce (R.box 0))⊕g(G.induce (R.box 1))).edgeSet.ncard=(G.induce R.chosen).edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rw [matchingEdges_sumGraph] at q
  rw [edge_ncard_sumGraph,R.box_edge_count cap 0,R.box_edge_count cap 1] at edgeQ
  have rank := rank_eq_of_graph_iso h
  rw [matchingEdges_sumGraph] at rank
  have edges : (G.induce R.chosen⊕g G.induce R.outside).edgeSet.ncard=(G.induce R.rootsᶜ).edgeSet.ncard := Nat.card_congr h.mapEdgeSet
  rw [edge_ncard_sumGraph] at edges
  have cost : (G.induce R.chosen).edgeSet.ncard=9*R.totalCapacity+8 := by dsimp only [totalCapacity];omega
  exact ⟨q.symm,cost,by rw [←rank,q.symm],by rw [←edges,cost]⟩

#print axioms separated_after_roots
#print axioms box_edge_count
#print axioms region_rank_edges
end JSP452Audit.StarHost.NinePortRegion
