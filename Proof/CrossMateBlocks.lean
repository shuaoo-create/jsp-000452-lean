import ClosedMateBarrier
import OddSmallAlphaMatching
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem lift_part_near (H : SimpleGraph X) (A U : Set X) (sub : A⊆U)
    (x : X) (hx : x∈A) (crit : PerfectAfterEveryDeletion (H.induce A)) :
    ∃ P : (H.induce U).Subgraph,P.IsMatching ∧ ∀v,v∈P.verts ↔ v.val∈A ∧ v.val≠x := by
  let a : A := ⟨x,hx⟩
  obtain ⟨p,hp⟩ := crit a
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

/-- With one edge across disjoint factor-critical parts, join their
near-perfect matchings through precisely the two remaining vertices. -/
theorem cross_edge_perfect_union (H : SimpleGraph X) (A B : Set X) (apart : Disjoint A B)
    (ca : PerfectAfterEveryDeletion (H.induce A)) (cb : PerfectAfterEveryDeletion (H.induce B))
    {x y : X} (hx : x∈A) (hy : y∈B) (xy : H.Adj x y) :
    ∃P : (H.induce (A∪B)).Subgraph,P.IsPerfectMatching := by
  let G := H.induce (A∪B)
  let a : ↥(A∪B) := ⟨x,Or.inl hx⟩
  let b : ↥(A∪B) := ⟨y,Or.inr hy⟩
  have e : G.Adj a b := xy
  obtain ⟨L,ml,sl⟩ := lift_part_near H A (A∪B) Set.subset_union_left x hx ca
  obtain ⟨R,mr,sr⟩ := lift_part_near H B (A∪B) Set.subset_union_right y hy cb
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

theorem critical_mate_blocks_separated (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (ne : w≠u) (cw : PerfectAfterEveryDeletion (H.induce (mateBlock H N w)))
    (cu : PerfectAfterEveryDeletion (H.induce (mateBlock H N u))) :
    ∀x∈mateBlock H N w,∀y∈mateBlock H N u,¬H.Adj x y := by
  intro x hx y hy adj
  exact (two_mate_blocks_not_perfect H N hm max w u hw hu).1
    (cross_edge_perfect_union H _ _ (different_mate_blocks_disjoint H N hm max w u hw hu ne)
      cw cu hx hy adj)

private theorem clique_odd_critical (H : SimpleGraph X) (A : Set X) (cl : H.IsClique A)
    (odd : Odd A.ncard) : PerfectAfterEveryDeletion (H.induce A) := by
  apply critical_of_odd_small_alpha
  · simpa only [Nat.card_coe_set_eq] using odd
  · intro x y z xy _ _
    exact Or.inl (cl x.property y.property (fun eq => xy (Subtype.ext eq)))
  · intro v a b
    by_cases eq : a=b
    · exact eq ▸ Reachable.refl a
    · have original : a.val.val≠b.val.val := fun he => eq (Subtype.ext (Subtype.ext he))
      exact (show ((H.induce A).induce {x|x≠v}).Adj a b from
        cl a.val.property b.val.property original).reachable

/-- In particular there is no host edge between distinct clique blocks. -/
theorem clique_mate_blocks_separated (H : SimpleGraph X) (N : H.Subgraph) (hm : N.IsMatching)
    (max : N.edgeSet.ncard=matchingEdges H) (w u : X) (hw : w∉N.verts) (hu : u∉N.verts)
    (ne : w≠u) (cw : H.IsClique (mateBlock H N w)) (cu : H.IsClique (mateBlock H N u)) :
    ∀x∈mateBlock H N w,∀y∈mateBlock H N u,¬H.Adj x y :=
  critical_mate_blocks_separated H N hm max w u hw hu ne
    (clique_odd_critical H _ cw (mateBlock_odd H N hm w hw))
    (clique_odd_critical H _ cu (mateBlock_odd H N hm u hu))

#print axioms cross_edge_perfect_union
#print axioms critical_mate_blocks_separated
#print axioms clique_mate_blocks_separated
end JSP452Audit.StarHost
