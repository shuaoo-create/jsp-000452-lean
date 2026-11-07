import NoThreeAugment

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Exchange a matched edge a–b for the host edge x–a at an uncovered x.
The new matching has the same size and moves exactly this hole from x to b.
Every old matching edge disjoint from a,b survives. -/
theorem shift_matching_hole (G : SimpleGraph X) (M : G.Subgraph) (hm : M.IsMatching)
    {x a b : X} (hx : x∉M.verts) (ab : M.Adj a b) (xa : G.Adj x a) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.edgeSet.ncard=M.edgeSet.ncard ∧
      N.verts=insert x (M.verts\{b}) ∧ N.Adj x a ∧
      ∀{c d : X}, M.Adj c d → c∉({a,b} : Set X) → d∉({a,b} : Set X) → N.Adj c d := by
  classical
  let rest := M.deleteVerts {a,b}
  let one := G.subgraphOfAdj xa
  have aUsed := M.edge_vert ab
  have bUsed := M.edge_vert ab.symm
  have distinct := (M.adj_sub ab).ne
  have restV : rest.verts=M.verts\{a,b} := rfl
  have oneV : one.verts={x,a} := rfl
  have apart : Disjoint rest.verts one.verts := by
    rw [Set.disjoint_left,restV,oneV]
    simp only [Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have paired := Padded.matching_sup_of_disjoint_verts G (matching_delete_pair G M hm ab)
    (Subgraph.IsMatching.subgraphOfAdj xa) apart
  have support : (rest⊔one).verts=insert x (M.verts\{b}) := by
    rw [Subgraph.verts_sup,restV,oneV]
    ext z
    simp only [Set.mem_union,Set.mem_sdiff,Set.mem_insert_iff,Set.mem_singleton_iff]
    grind
  have size := congrArg Set.ncard support
  have fresh : x∉M.verts\{b} := fun h => hx h.1
  rw [matching_vertices_eq_twice_edges paired,Set.ncard_insert_of_notMem fresh] at size
  have before := Set.ncard_sdiff_singleton_add_one bUsed
  rw [matching_vertices_eq_twice_edges hm] at before
  have count : 2*(rest⊔one).edgeSet.ncard=2*M.edgeSet.ncard := size.trans before
  refine ⟨rest⊔one,paired,by omega,support,Or.inr (G.subgraphOfAdj_adj_self xa),?_⟩
  intro c d cd cout dout
  exact Or.inl (Subgraph.deleteVerts_adj.mpr ⟨M.edge_vert cd,cout,M.edge_vert cd.symm,dout,cd⟩)

/-- Two exposed vertices cannot be joined by an alternating five-edge path
through two disjoint edges of a maximum matching. -/
theorem no_five_augment_of_disjoint (G : SimpleGraph X) (M : G.Subgraph) (hm : M.IsMatching)
    (maximum : M.edgeSet.ncard=matchingEdges G) {x y a b c d : X}
    (hx : x∉M.verts) (hy : y∉M.verts) (hxy : x≠y)
    (ab : M.Adj a b) (cd : M.Adj c d) (apart : Disjoint ({a,b} : Set X) {c,d})
    (xa : G.Adj x a) (bc : G.Adj b c) (dy : G.Adj d y) : False := by
  obtain ⟨N,hn,size,support,_,kept⟩ := shift_matching_hole G M hm hx ab xa
  have bUsed := M.edge_vert ab.symm
  have bx : b≠x := fun eq => hx (eq ▸ bUsed)
  have byNe : b≠y := fun eq => hy (eq ▸ bUsed)
  have bFree : b∉N.verts := by simp [support,bx]
  have yFree : y∉N.verts := by simp [support,hxy.symm,hy]
  have cout : c∉({a,b} : Set X) := fun hc => Set.disjoint_left.mp apart hc (Set.mem_insert c {d})
  have dout : d∉({a,b} : Set X) := fun hd => Set.disjoint_left.mp apart hd (by simp)
  exact no_three_augment G N hn (size.trans maximum) bFree yFree byNe (kept cd cout dout) bc dy

/-- The same conclusion with no disjointness premise. If the two matched
edges coincide, matching uniqueness shortens the walk to three edges. -/
theorem no_five_augment (G : SimpleGraph X) (M : G.Subgraph) (hm : M.IsMatching)
    (maximum : M.edgeSet.ncard=matchingEdges G) {x y a b c d : X}
    (hx : x∉M.verts) (hy : y∉M.verts) (hxy : x≠y)
    (ab : M.Adj a b) (cd : M.Adj c d)
    (xa : G.Adj x a) (bc : G.Adj b c) (dy : G.Adj d y) : False := by
  by_cases ac : a=c
  · subst c
    have bd := hm.eq_of_adj_left ab cd
    subst d
    exact no_three_augment G M hm maximum hx hy hxy ab xa dy
  · have cb : b≠c := bc.ne
    have ad : a≠d := by
      intro eq
      subst d
      exact cb (hm.eq_of_adj_left ab cd.symm)
    have bd : b≠d := by
      intro eq
      subst d
      exact ac (hm.eq_of_adj_right ab cd)
    have apart : Disjoint ({a,b} : Set X) {c,d} := by
      rw [Set.disjoint_left]
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
      grind
    exact no_five_augment_of_disjoint G M hm maximum hx hy hxy ab cd apart xa bc dy

#print axioms shift_matching_hole
#print axioms no_five_augment_of_disjoint
#print axioms no_five_augment
end JSP452Audit.StarHost
