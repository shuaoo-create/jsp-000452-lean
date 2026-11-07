import ExposableMatePair
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem lift_point_exposed (H : SimpleGraph X) (A U : Set X) (sub : A⊆U)
    (x : X) (hx : x∈A) (ex : ExposablePoint (H.induce A) ⟨x,hx⟩) :
    ∃ P : (H.induce U).Subgraph,P.IsMatching ∧ ∀v,v∈P.verts ↔ v.val∈A ∧ v.val≠x := by
  let a : A := ⟨x,hx⟩
  obtain ⟨p,hp⟩ := ex
  obtain ⟨m,hm,supp,_⟩ := lift_perfect_off_vertex_maximum (H.induce A) a p hp
  let e : H.induce A →g H.induce U := {
    toFun := fun v => ⟨v.val,sub v.property⟩
    map_rel' := fun h => h }
  have inj : Function.Injective e := fun l r eq => Subtype.ext (congrArg (fun v : U => v.val) eq)
  refine ⟨m.map e,hm.map e inj,?_⟩
  intro v
  rw [Subgraph.map_verts,supp]
  constructor
  · rintro ⟨b,hb,rfl⟩
    exact ⟨b.property,fun eq => hb (Subtype.ext eq)⟩
  · rintro ⟨ha,ne⟩
    exact ⟨⟨v.val,ha⟩,fun eq => ne (congrArg Subtype.val eq),Subtype.ext rfl⟩

/-- Pointwise extension of the earlier factor-critical union lemma: only
these particular endpoints need to be exposable in their own parts. -/
theorem exposed_cross_perfect_union (H : SimpleGraph X) (A B : Set X) (apart : Disjoint A B)
    {x y : X} (hx : x∈A) (hy : y∈B) (ca : ExposablePoint (H.induce A) ⟨x,hx⟩)
    (cb : ExposablePoint (H.induce B) ⟨y,hy⟩) (xy : H.Adj x y) :
    ∃P : (H.induce (A∪B)).Subgraph,P.IsPerfectMatching := by
  let G := H.induce (A∪B)
  let a : ↥(A∪B) := ⟨x,Or.inl hx⟩
  let b : ↥(A∪B) := ⟨y,Or.inr hy⟩
  have e : G.Adj a b := xy
  obtain ⟨L,ml,sl⟩ := lift_point_exposed H A (A∪B) Set.subset_union_left x hx ca
  obtain ⟨R,mr,sr⟩ := lift_point_exposed H B (A∪B) Set.subset_union_right y hy cb
  let E := G.subgraphOfAdj e
  have ee : E.verts={a,b} := rfl
  have lr : Disjoint L.verts R.verts := Set.disjoint_left.mpr
    (fun {p} l r => Set.disjoint_left.mp apart ((sl p).mp l).1 ((sr p).mp r).1)
  have m0 := JSP452Audit.Padded.matching_sup_of_disjoint_verts G ml mr lr
  have away : Disjoint (L⊔R).verts E.verts := by
    apply Set.disjoint_left.mpr
    intro p hp he
    rw [ee,Set.mem_insert_iff,Set.mem_singleton_iff] at he
    rw [Subgraph.verts_sup] at hp
    rcases he with rfl|rfl
    · rcases hp with l|r
      · exact ((sl a).mp l).2 rfl
      · exact Set.disjoint_left.mp apart hx ((sr a).mp r).1
    · rcases hp with l|r
      · exact Set.disjoint_left.mp apart ((sl b).mp l).1 hy
      · exact ((sr b).mp r).2 rfl
  have m := JSP452Audit.Padded.matching_sup_of_disjoint_verts G m0 (Subgraph.IsMatching.subgraphOfAdj e) away
  refine ⟨(L⊔R)⊔E,m,Subgraph.isSpanning_iff.mpr (Set.eq_univ_of_forall ?_)⟩
  intro p
  rw [Subgraph.verts_sup,Subgraph.verts_sup,ee]
  rcases p.property with h|h
  · by_cases ex : p.val=x
    · exact Or.inr (Or.inl (Subtype.ext ex))
    · exact Or.inl (Or.inl ((sl p).mpr ⟨h,ex⟩))
  · by_cases ey : p.val=y
    · exact Or.inr (Or.inr (Subtype.ext ey))
    · exact Or.inl (Or.inr ((sr p).mpr ⟨h,ey⟩))

theorem exposable_block_vertices_nonadjacent (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (ne : w≠u) (a : mateBlock H N w) (b : mateBlock H N u)
    (ea : ExposablePoint (H.induce (mateBlock H N w)) a)
    (eb : ExposablePoint (H.induce (mateBlock H N u)) b) : ¬H.Adj a.val b.val := by
  intro edge
  exact (two_mate_blocks_not_perfect H N hm max w u hw hu).1
    (exposed_cross_perfect_union H _ _ (different_mate_blocks_disjoint H N hm max w u hw hu ne)
      a.property b.property ea eb edge)

#print axioms exposed_cross_perfect_union
#print axioms exposable_block_vertices_nonadjacent
end JSP452Audit.StarHost
