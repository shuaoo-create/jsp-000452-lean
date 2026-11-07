import PackingFloor
import TutteJoin

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

variable {I X : Type*} (R K : SimpleGraph X) (n : I → ℕ) (f : (forest n).Copy (R ⊔ K))

/-- The exact original indices using an edge missing in R. An edge present
in both colors of this union does not mark its star as touched. -/
def touchedStars : Set I :=
  {i | ∃ j : Fin (n i), ¬ R.Adj (f (center n i)) (f (leaf n ⟨i,j⟩))}

theorem untouched_star_edge {i : I} (good : i ∉ touchedStars R K n f) (j : Fin (n i)) :
    R.Adj (f (center n i)) (f (leaf n ⟨i,j⟩)) := by
  by_contra no
  exact good ⟨j,no⟩

/-- All source edges of a component outside the touched set survive, with
the identical source-to-host vertex map. -/
theorem untouched_star_adjacency {x y : Vertices n} (good : x.1 ∉ touchedStars R K n f)
    (adj : (forest n).Adj x y) : R.Adj (f x) (f y) := by
  let e : (forest n).edgeSet := ⟨s(x,y),(forest n).mem_edgeSet.mpr adj⟩
  obtain ⟨p,h⟩ := (edgeEquiv n).surjective e
  have ends : s(center n p.1,leaf n p) = s(x,y) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp ends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · exact untouched_star_edge R K n f good p.2
  · exact (untouched_star_edge R K n f good p.2).symm

/-- One missing edge from each affected original star is realized by a single
matching inside K, with an explicit edge witness for each affected index. -/
theorem exists_touched_star_matching [Finite X] :
    ∃ M : K.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = (touchedStars R K n f).ncard ∧
      ∀ i ∈ touchedStars R K n f, ∃ j : Fin (n i),
        M.Adj (f (center n i)) (f (leaf n ⟨i,j⟩)) ∧ ¬ R.Adj (f (center n i)) (f (leaf n ⟨i,j⟩)) := by
  let B := touchedStars R K n f
  let idx (i : B) : Fin (n i.val) := i.property.choose
  let l : B ↪ X := ⟨fun i => f (center n i.val),
    fun _ _ e => Subtype.ext (congrArg Sigma.fst (f.injective e))⟩
  let r : B ↪ X := ⟨fun i => f (leaf n ⟨i.val,idx i⟩),
    fun _ _ e => Subtype.ext (congrArg Sigma.fst (f.injective e))⟩
  have edges (i : B) : K.Adj (l i) (r i) :=
    (f.toHom.map_adj (starEdge n ⟨i.val,idx i⟩)).resolve_left i.property.choose_spec
  have apart : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,e⟩
    exact leaf_ne_center n ⟨j.val,idx j⟩ i.val (f.injective e)
  let M := pairFamily K l r edges
  have hm := pairFamily_isMatching K l r edges apart
  have vl : M.verts.ncard = B.ncard+B.ncard := by
    change (Set.range l ∪ Set.range r).ncard = _
    rw [Set.ncard_union_eq apart,Set.ncard_range_of_injective l.injective,
      Set.ncard_range_of_injective r.injective]
    rfl
  have count := matching_vertices_eq_twice_edges hm
  change M.verts.ncard = 2*M.edgeSet.ncard at count
  refine ⟨M,hm,by change M.edgeSet.ncard=B.ncard; omega,?_⟩
  intro i hit
  let b : B := ⟨i,hit⟩
  exact ⟨idx b,Or.inl ⟨b,rfl,rfl⟩,b.property.choose_spec⟩

theorem touchedStars_le_matchingEdges [Finite X] : (touchedStars R K n f).ncard ≤ matchingEdges K := by
  obtain ⟨M,hm,eq,_⟩ := exists_touched_star_matching R K n f
  exact eq ▸ le_matchingEdges hm

#print axioms exists_touched_star_matching
#print axioms touchedStars_le_matchingEdges
#print axioms untouched_star_adjacency
end JSP452Audit.StarHost
