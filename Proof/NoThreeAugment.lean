import MissedNeighbor
namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Deleting both ends of an actual matched edge preserves every other matched pair. -/
theorem matching_delete_pair (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    {a b : X} (ab : M.Adj a b) : (M.deleteVerts {a,b}).IsMatching := by
  intro u hu
  change u ∈ M.verts \ {a,b} at hu
  obtain ⟨w,uw,_⟩ := hM hu.1
  have kept : w ∉ ({a,b} : Set X) := by
    rintro (rfl | h)
    · have eq := hM.eq_of_adj_right uw ab.symm
      exact hu.2 (Or.inr (Set.mem_singleton_iff.mpr eq))
    · obtain rfl := Set.mem_singleton_iff.mp h
      have eq := hM.eq_of_adj_right uw ab
      exact hu.2 (Or.inl eq)
  have wmem := M.edge_vert uw.symm
  refine ⟨w,Subgraph.deleteVerts_adj.mpr ⟨hu.1,hu.2,wmem,kept,uw⟩,?_⟩
  intro z hz
  exact hM.eq_of_adj_left (Subgraph.deleteVerts_adj.mp hz).2.2.2.2 uw

/-- Replace the middle matched edge with two true host edges, increasing the
number of matching edges by exactly one. -/
theorem augment_three_edges [Finite X] (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    {x y a b : X} (hx : x ∉ M.verts) (hy : y ∉ M.verts) (hxy : x ≠ y)
    (ab : M.Adj a b) (xa : G.Adj x a) (byEdge : G.Adj b y) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  classical
  let rest := M.deleteVerts {a,b}
  let left := G.subgraphOfAdj xa
  let right := G.subgraphOfAdj byEdge
  have aM : a ∈ M.verts := M.edge_vert ab
  have bM : b ∈ M.verts := M.edge_vert ab.symm
  have hab : a ≠ b := (M.adj_sub ab).ne
  have restEq : rest.verts = M.verts \ {a,b} := rfl
  have leftEq : left.verts = {x,a} := rfl
  have rightEq : right.verts = {b,y} := rfl
  have dis1 : Disjoint rest.verts left.verts := by
    rw [Set.disjoint_left,restEq,leftEq]
    simp only [Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have dis2 : Disjoint (rest ⊔ left).verts right.verts := by
    rw [Set.disjoint_left,Subgraph.verts_sup,restEq,leftEq,rightEq]
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have ml := Padded.matching_sup_of_disjoint_verts G
    (matching_delete_pair G M hM ab) (Subgraph.IsMatching.subgraphOfAdj xa) dis1
  have mn := Padded.matching_sup_of_disjoint_verts G ml (Subgraph.IsMatching.subgraphOfAdj byEdge) dis2
  have verts : ((rest ⊔ left) ⊔ right).verts = insert x (insert y M.verts) := by
    rw [Subgraph.verts_sup,Subgraph.verts_sup,restEq,leftEq,rightEq]
    ext z
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have fresh : x ∉ insert y M.verts := by simpa [hx] using hxy
  have total := congrArg Set.ncard verts
  rw [matching_vertices_eq_twice_edges mn,Set.ncard_insert_of_notMem fresh,
    Set.ncard_insert_of_notMem hy,matching_vertices_eq_twice_edges hM] at total
  exact ⟨_,mn,by omega⟩

theorem no_three_augment [Finite X] (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    (maximum : M.edgeSet.ncard = matchingEdges G) {x y a b : X}
    (hx : x ∉ M.verts) (hy : y ∉ M.verts) (hxy : x ≠ y)
    (ab : M.Adj a b) (xa : G.Adj x a) (byEdge : G.Adj b y) : False := by
  obtain ⟨N,hN,larger⟩ := augment_three_edges G M hM hx hy hxy ab xa byEdge
  have bounded := le_matchingEdges hN
  omega

#print axioms matching_delete_pair
#print axioms augment_three_edges
#print axioms no_three_augment
end JSP452Audit.StarHost
