import TutteJoin
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A maximum matching cannot leave both endpoints of a genuine edge unmatched. -/
theorem missed_neighbors_subset {X : Type*} [Finite X] (G : SimpleGraph X)
    (M : G.Subgraph) (hM : M.IsMatching) (maximum : M.edgeSet.ncard = matchingEdges G)
    {x : X} (hx : x ∉ M.verts) : G.neighborSet x ⊆ M.verts := by
  intro y edge
  by_contra hy
  let one := G.subgraphOfAdj edge
  have sub : Disjoint M.verts one.verts := by
    apply Set.disjoint_left.mpr
    intro v h used
    change v ∈ {x,y} at used
    rcases Set.mem_insert_iff.mp used with rfl | hy'
    · exact hx h
    · exact hy ((Set.mem_singleton_iff.mp hy') ▸ h)
  have augmented : (M ⊔ one).IsMatching :=
    Padded.matching_sup_of_disjoint_verts G hM (Subgraph.IsMatching.subgraphOfAdj edge) sub
  have larger : M.verts ⊂ (M ⊔ one).verts := by
    refine ⟨fun _ h => Or.inl h,fun back => hx (back ?_)⟩
    exact Or.inr (Set.mem_insert x {y})
  have grew := Set.ncard_lt_ncard larger
  rw [matching_vertices_eq_twice_edges hM,matching_vertices_eq_twice_edges augmented,maximum] at grew
  have le := le_matchingEdges augmented
  omega

theorem missed_degree_le_twice_rank {X : Type*} [Finite X] (G : SimpleGraph X)
    (M : G.Subgraph) (hM : M.IsMatching) (maximum : M.edgeSet.ncard = matchingEdges G)
    {x : X} (hx : x ∉ M.verts) : Nat.card (G.neighborSet x) ≤ 2 * matchingEdges G := by
  have h := Set.ncard_le_ncard (missed_neighbors_subset G M hM maximum hx)
  rw [matching_vertices_eq_twice_edges hM,maximum] at h
  exact h

#print axioms missed_neighbors_subset
#print axioms missed_degree_le_twice_rank
end JSP452Audit.StarHost
