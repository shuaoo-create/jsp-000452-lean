import NineComponentColoring
import NoThreeAugment
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- One end of a matched edge sees all uncovered neighbors of either end.
Otherwise the two missing adjacencies give a three-edge augmentation. -/
private theorem orient_mate_for_holes (G : SimpleGraph X) (M : G.Subgraph)
    (hm : M.IsMatching) (max : M.edgeSet.ncard=matchingEdges G) {a b}
    (ab : M.Adj a b) :
    (∀w,w∉M.verts → G.Adj w b → G.Adj w a) ∨
      (∀w,w∉M.verts → G.Adj w a → G.Adj w b) := by
  classical
  by_cases h : ∀w,w∉M.verts → G.Adj w b → G.Adj w a
  · exact Or.inl h
  · push Not at h
    obtain ⟨v,hv,vb,va⟩ := h
    right
    intro w hw wa
    by_cases eq : w=v
    · exact eq ▸ vb
    · exact (no_three_augment G M hm max hw hv eq ab wa vb.symm).elim

private theorem choose_center_on_edge (G : SimpleGraph X) (M : G.Subgraph)
    (hm : M.IsMatching) (max : M.edgeSet.ncard=matchingEdges G)
    (e : Sym2 X) (he : e∈M.edgeSet) :
    ∃z,z∈e ∧ ∀u∈e,(u=z ∨ G.Adj u z) ∧
      ∀w,w∉M.verts → G.Adj w u → G.Adj w z := by
  induction e using Sym2.inductionOn with
  | _ a b =>
    have ab : M.Adj a b := he
    have edge := M.adj_sub ab
    rcases orient_mate_for_holes G M hm max ab with left|right
    · refine ⟨a,Sym2.mem_mk_left _ _,?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl|rfl
      · exact ⟨Or.inl rfl,fun _ _ h => h⟩
      · exact ⟨Or.inr edge.symm,left⟩
    · refine ⟨b,Sym2.mem_mk_right _ _,?_⟩
      intro u hu
      rcases Sym2.mem_iff.mp hu with rfl|rfl
      · exact ⟨Or.inr edge,right⟩
      · exact ⟨Or.inl rfl,fun _ _ h => h⟩

/-- All nonisolated vertices can be dominated at cost at most the actual
matching number. Isolated vertices do not enter the cover requirement. -/
theorem centers_at_matching_rank (G : SimpleGraph X) :
    ∃S : Set X,S.ncard≤matchingEdges G ∧
      ∀x,(∃y,G.Adj x y) → x∉S → ∃z∈S,G.Adj x z := by
  classical
  obtain ⟨M,hm,max⟩ := exists_maximum_matching G
  have pick (e : M.edgeSet) := choose_center_on_edge G M hm max e.val e.property
  choose center membership prop using pick
  let S := Set.range center
  have size : S.ncard≤M.edgeSet.ncard := by
    rw [←Nat.card_coe_set_eq,←Nat.card_coe_set_eq]
    exact Nat.card_le_card_of_surjective (f:=Set.rangeFactorization center)
      (by rintro ⟨v,e,rfl⟩;exact ⟨e,rfl⟩)
  refine ⟨S,size.trans max.le,?_⟩
  intro x noniso outside
  by_cases used : x∈M.verts
  · obtain ⟨y,xy,_⟩ := hm used
    let e : M.edgeSet := ⟨s(x,y),xy⟩
    have cover := (prop e x (Sym2.mem_mk_left x y)).1
    refine ⟨center e,Set.mem_range_self e,cover.resolve_left ?_⟩
    exact fun eq => outside ⟨e,eq.symm⟩
  · obtain ⟨y,xy⟩ := noniso
    obtain ⟨z,yz,_⟩ := hm (missed_neighbors_subset G M hm max used xy)
    let e : M.edgeSet := ⟨s(y,z),yz⟩
    exact ⟨center e,Set.mem_range_self e,(prop e y (Sym2.mem_mk_left y z)).2 x used xy⟩

#print axioms centers_at_matching_rank
end JSP452Audit.StarHost
