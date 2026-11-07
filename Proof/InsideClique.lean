import EdgeSplit
import NoThreeAugment
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Select precisely k actual matching edges, keeping only their incident vertices. -/
theorem select_matching_edges (F : SimpleGraph X) (M : F.Subgraph) (hm : M.IsMatching)
    (k : ℕ) (bound : k ≤ M.edgeSet.ncard) :
    ∃ N : F.Subgraph, N.IsMatching ∧ N.edgeSet.ncard = k ∧ N.verts ⊆ M.verts := by
  obtain ⟨R,le,card,_⟩ := exists_edge_split M.spanningCoe k bound
  let N : F.Subgraph := {
    verts := R.support
    Adj := R.Adj
    adj_sub := fun h => M.adj_sub (le h)
    edge_vert := fun h => ⟨_,h⟩
    symm := ⟨fun _ _ h => h.symm⟩ }
  refine ⟨N,?_,card,?_⟩
  · rintro x ⟨y,xy⟩
    exact ⟨y,xy,fun z xz => hm.eq_of_adj_left (le xz) (le xy)⟩
  · rintro x ⟨y,xy⟩
    exact M.edge_vert (le xy)

/-- Remove the edge touching x, if any. This retains a real matching missing x
and costs at most one edge. -/
private theorem avoid_one (F : SimpleGraph X) (M : F.Subgraph) (hm : M.IsMatching) (x : X) :
    ∃ N : F.Subgraph, N.IsMatching ∧ N.verts ⊆ M.verts ∧ x ∉ N.verts ∧
      M.edgeSet.ncard ≤ N.edgeSet.ncard+1 := by
  classical
  by_cases used : x∈M.verts
  · obtain ⟨y,xy,_⟩ := hm used
    let N := M.deleteVerts {x,y}
    have hn : N.IsMatching := matching_delete_pair F M hm xy
    have sub : ({x,y} : Set X) ⊆ M.verts := by
      intro w hw; rcases hw with h | h
      · exact h ▸ used
      · exact (Set.mem_singleton_iff.mp h) ▸ M.edge_vert xy.symm
    have count := Set.ncard_sdiff' sub
    have diff := (M.adj_sub xy).ne
    change N.verts.ncard = M.verts.ncard - ({x,y}:Set X).ncard at count
    rw [matching_vertices_eq_twice_edges hn, matching_vertices_eq_twice_edges hm,
      Set.ncard_pair diff] at count
    exact ⟨N,hn,fun _ h => h.1,fun h => h.2 (Set.mem_insert x {y}),by omega⟩
  · exact ⟨M,hm,Set.Subset.rfl,used,by omega⟩

/-- If all size-m0 matchings leave a clique, a maximum matching misses at most
one vertex, and hence survives avoidance of two prescribed vertices with at least m0 edges. -/
theorem complete_of_unmatched_cliques (F : SimpleGraph X) (m0 u : ℕ)
    (order : Nat.card X = 2*m0+u+1) (large : 3 ≤ u) (enough : m0 ≤ matchingEdges F)
    (clique : ∀ M : F.Subgraph, M.IsMatching → M.edgeSet.ncard = m0 → F.IsClique M.vertsᶜ) :
    F = ⊤ := by
  classical
  obtain ⟨M,hm,max⟩ := exists_maximum_matching F
  obtain ⟨N,hn,card,sub⟩ := select_matching_edges F M hm m0 (enough.trans_eq max.symm)
  have cm := clique N hn card
  have few : M.vertsᶜ.ncard ≤ 1 := by
    apply (Set.ncard_le_one (s := M.vertsᶜ)).mpr
    intro x hx y hy
    by_contra diff
    have edge := cm (fun used => hx (sub used)) (fun used => hy (sub used)) diff
    exact hy (missed_neighbors_subset F M hm max hx edge)
  have total := Set.ncard_add_ncard_compl M.verts
  rw [matching_vertices_eq_twice_edges hm] at total
  have reserve : m0+2 ≤ M.edgeSet.ncard := by omega
  apply top_unique
  intro x y distinct
  obtain ⟨P,hp,_,missX,px⟩ := avoid_one F M hm x
  obtain ⟨Q,hq,qp,missY,qy⟩ := avoid_one F P hp y
  obtain ⟨T,ht,ct,tq⟩ := select_matching_edges F Q hq m0 (by omega)
  exact clique T ht ct (fun used => missX (qp (tq used))) (fun used => missY (tq used)) distinct

#print axioms select_matching_edges
#print axioms complete_of_unmatched_cliques
end JSP452Audit.StarHost
