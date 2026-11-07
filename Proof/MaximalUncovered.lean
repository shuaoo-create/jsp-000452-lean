import MissedNeighbor
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Inclusion-maximal matching is exactly independence of the original uncovered set. -/
theorem maximal_matching_iff_uncovered_independent {X : Type*} (G : SimpleGraph X)
    (M : G.Subgraph) (hm : M.IsMatching) :
    (∀ N : G.Subgraph, N.IsMatching → M ≤ N → M = N) ↔ G.IsIndepSet M.vertsᶜ := by
  constructor
  · intro maximal x hx y hy _ edge
    let one := G.subgraphOfAdj edge
    have dis : Disjoint M.verts one.verts := by
      apply Set.disjoint_left.mpr
      rintro w used (rfl | hit)
      · exact hx used
      · exact hy ((Set.mem_singleton_iff.mp hit) ▸ used)
    have larger := Padded.matching_sup_of_disjoint_verts G hm
      (Subgraph.IsMatching.subgraphOfAdj edge) dis
    have eq := maximal (M ⊔ one) larger le_sup_left
    have fresh : x ∈ (M ⊔ one).verts := Or.inr (Set.mem_insert x {y})
    exact hx (eq.symm ▸ fresh)
  · intro independent N hN incl
    have ifMatched {x y : X} (hx : x ∈ M.verts) (edge : N.Adj x y) : M.Adj x y := by
      obtain ⟨w,xw,_⟩ := hm hx
      have eq : w = y := hN.eq_of_adj_left (incl.2 xw) edge
      exact eq ▸ xw
    have retained {x y : X} (edge : N.Adj x y) : M.Adj x y := by
      by_cases old : x ∈ M.verts
      · exact ifMatched old edge
      by_cases other : y ∈ M.verts
      · exact (ifMatched other edge.symm).symm
      exact (independent old other (N.adj_sub edge).ne (N.adj_sub edge)).elim
    apply le_antisymm incl
    refine ⟨?_,fun _ _ edge => retained edge⟩
    intro x used
    obtain ⟨w,xw,_⟩ := hN used
    exact M.edge_vert (retained xw)

/-- The original matched pairs form a perfect matching on the subgraph
induced by all covered original vertices. -/
theorem perfect_on_matched_verts {X : Type*} (G : SimpleGraph X) (M : G.Subgraph) (hm : M.IsMatching) :
    ∃ N : (G.induce M.verts).Subgraph, N.IsPerfectMatching := by
  have incl : M.coe ≤ G.induce M.verts := fun _ _ h => M.adj_sub h
  let N := (G.induce M.verts).toSubgraph M.coe incl
  refine ⟨N,?_,fun x => Set.mem_univ x⟩
  intro x _
  obtain ⟨w,edge,unique⟩ := hm x.property
  exact ⟨⟨w,M.edge_vert edge.symm⟩,edge,fun z hz => Subtype.ext (unique z.val hz)⟩

theorem matchingEdges_on_matched_verts {X : Type*} [Finite X] (G : SimpleGraph X)
    (M : G.Subgraph) (hm : M.IsMatching) :
    matchingEdges (G.induce M.verts) = M.edgeSet.ncard := by
  obtain ⟨N,hN⟩ := perfect_on_matched_verts G M hm
  obtain ⟨K,hK,maximum⟩ := exists_maximum_matching (G.induce M.verts)
  have span := matching_vertices_eq_twice_edges hN.1
  rw [Subgraph.isSpanning_iff.mp hN.2,Set.ncard_univ,Nat.card_coe_set_eq,
    matching_vertices_eq_twice_edges hm] at span
  have bound := Set.ncard_le_ncard (Set.subset_univ K.verts)
  rw [Set.ncard_univ,Nat.card_coe_set_eq,matching_vertices_eq_twice_edges hm,
    matching_vertices_eq_twice_edges hK,maximum] at bound
  have lower := le_matchingEdges hN.1
  omega

#print axioms maximal_matching_iff_uncovered_independent
#print axioms perfect_on_matched_verts
#print axioms matchingEdges_on_matched_verts
end JSP452Audit.StarHost
