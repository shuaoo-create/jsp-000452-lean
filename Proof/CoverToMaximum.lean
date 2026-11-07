import NoThreeAugment

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem delete_pair_card (G : SimpleGraph X) (M : G.Subgraph) (hM : M.IsMatching)
    {a b : X} (ab : M.Adj a b) :
    (M.deleteVerts {a,b}).edgeSet.ncard + 1 = M.edgeSet.ncard := by
  have sub : ({a,b} : Set X) ⊆ M.verts := by
    rintro z (rfl | hz)
    · exact M.edge_vert ab
    · exact (Set.mem_singleton_iff.mp hz).symm ▸ M.edge_vert ab.symm
  have count := Set.ncard_sdiff_add_ncard_of_subset sub
  have pair : ({a,b} : Set X).ncard = 2 := by simp [(M.adj_sub ab).ne]
  rw [pair, ← (Subgraph.deleteVerts_verts (G' := M) (s := {a,b})),
    matching_vertices_eq_twice_edges (matching_delete_pair G M hM ab),
    matching_vertices_eq_twice_edges hM] at count
  omega

/-- Remove at most one edge of Q to avoid y as well as its already-uncovered x. -/
private theorem trim_one (G : SimpleGraph X) (Q : G.Subgraph) (hQ : Q.IsMatching)
    {x y : X} (hx : x ∉ Q.verts) :
    ∃ R : G.Subgraph, R.IsMatching ∧ R.verts ⊆ Q.verts ∧ x ∉ R.verts ∧ y ∉ R.verts ∧
      Q.edgeSet.ncard ≤ R.edgeSet.ncard + 1 := by
  by_cases hy : y ∈ Q.verts
  · obtain ⟨z,yz,_⟩ := hQ hy
    refine ⟨Q.deleteVerts {y,z},matching_delete_pair G Q hQ yz,
      (fun _ h => h.1),(fun h => hx h.1),(fun h => h.2 (Set.mem_insert _ _)),?_⟩
    exact (delete_pair_card G Q hQ yz).ge
  · exact ⟨Q,hQ,Set.Subset.rfl,hx,hy,by omega⟩

/-- Extend vertex coverage up to the size of a comparison matching, using only
vertices in the two given matchings. The latter condition preserves frozen pairs. -/
theorem cover_matching_up_to (G : SimpleGraph X) (P Q : G.Subgraph)
    (hP : P.IsMatching) (hQ : Q.IsMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧ P.verts ⊆ N.verts ∧
      Q.edgeSet.ncard ≤ N.edgeSet.ncard ∧ N.verts ⊆ P.verts ∪ Q.verts := by
  suffices aux : ∀ n (P Q : G.Subgraph), P.IsMatching → Q.IsMatching → P.edgeSet.ncard = n →
      ∃ N : G.Subgraph, N.IsMatching ∧ P.verts ⊆ N.verts ∧
        Q.edgeSet.ncard ≤ N.edgeSet.ncard ∧ N.verts ⊆ P.verts ∪ Q.verts from
    aux _ P Q hP hQ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro P Q hP hQ size
    classical
    by_cases covered : P.verts ⊆ Q.verts
    · exact ⟨Q,hQ,covered,le_rfl,Set.subset_union_right⟩
    obtain ⟨x,px,qx⟩ := Set.not_subset.mp covered
    obtain ⟨y,xy,_⟩ := hP px
    let P' := P.deleteVerts {x,y}
    have mP' : P'.IsMatching := matching_delete_pair G P hP xy
    have cardP' : P'.edgeSet.ncard + 1 = P.edgeSet.ncard := delete_pair_card G P hP xy
    obtain ⟨Q',mQ',subQ,qx',qy',loss⟩ := trim_one (y := y) G Q hQ qx
    obtain ⟨N,mN,coverN,szN,subN⟩ := ih P'.edgeSet.ncard (by omega) P' Q' mP' mQ' rfl
    let one := G.subgraphOfAdj (P.adj_sub xy)
    have ss : one.verts = {x,y} := rfl
    have dis : Disjoint N.verts one.verts := by
      apply Set.disjoint_left.mpr
      intro z hz hp
      rw [ss] at hp
      rcases subN hz with left | right
      · exact left.2 hp
      · rcases Set.mem_insert_iff.mp hp with rfl | hp
        · exact qx' right
        · exact qy' ((Set.mem_singleton_iff.mp hp) ▸ right)
    have mplus := Padded.matching_sup_of_disjoint_verts G mN
      (Subgraph.IsMatching.subgraphOfAdj (P.adj_sub xy)) dis
    have nplus : (N ⊔ one).edgeSet.ncard = N.edgeSet.ncard + 1 := by
      have vertices := Set.ncard_union_eq dis
      have two : one.verts.ncard = 2 := by rw [ss]; simp [(P.adj_sub xy).ne]
      rw [← Subgraph.verts_sup,matching_vertices_eq_twice_edges mplus,
        matching_vertices_eq_twice_edges mN,two] at vertices
      change 2 * (N ⊔ one).edgeSet.ncard = 2 * N.edgeSet.ncard + 2 at vertices
      omega
    refine ⟨N ⊔ one,mplus,?_,by omega,?_⟩
    · intro z pz
      by_cases zp : z ∈ ({x,y} : Set X)
      · exact Or.inr zp
      · exact Or.inl (coverN ⟨pz,zp⟩)
    · intro z hz
      rcases hz with hz | hz
      · rcases subN hz with left | right
        · exact Or.inl left.1
        · exact Or.inr (subQ right)
      · rw [ss] at hz
        rcases Set.mem_insert_iff.mp hz with rfl | hz
        · exact Or.inl px
        · exact Or.inl ((Set.mem_singleton_iff.mp hz).symm ▸ P.edge_vert xy.symm)

/-- A genuine maximum matching can be chosen to cover all vertices of P. -/
theorem exists_maximum_matching_covering (G : SimpleGraph X) (P : G.Subgraph)
    (hP : P.IsMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.edgeSet.ncard = matchingEdges G ∧ P.verts ⊆ N.verts := by
  obtain ⟨Q,hQ,maximum⟩ := exists_maximum_matching G
  obtain ⟨N,hN,cover,large,_⟩ := cover_matching_up_to G P Q hP hQ
  exact ⟨N,hN,le_antisymm (le_matchingEdges hN) (maximum ▸ large),cover⟩

#print axioms cover_matching_up_to
#print axioms exists_maximum_matching_covering
end JSP452Audit.StarHost
