import SingleEmbeddedHeadExclusion
import WholeCoreErasureRank
open private JSP452Audit.StarHost.matchingInColour JSP452Audit.StarHost.matchingInColour_matching from WholeCoreErasureRank
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem in_internal_colour (G : SimpleGraph X) (P : Set X) (v w:X) :
    (G \ eraseInternal G P).Adj v w ↔ G.Adj v w ∧ v∈P ∧ w∈P := by
  classical
  change (G.Adj v w ∧ ¬(G.Adj v w ∧ ¬(v∈P ∧ w∈P))) ↔ _
  tauto

/-- For the same matching, separate core vertices paired internally from
those with an external mate. External mates are distinct actual roots. -/
theorem protected_matching_counts (G : SimpleGraph X) (P A : Set X) (apart : Disjoint P A)
    (outside : ∀v∈P,∀w,G.Adj v w → w∉P → w∈A) (M : G.Subgraph) (hm : M.IsMatching) :
    let T := P∩M.verts
    T.ncard≤2*matchingEdges (G.induce P)+A.ncard ∧
      2*T.ncard≤2*matchingEdges (G.induce (P∪A))+2*matchingEdges (G.induce P) := by
  classical
  intro T
  let L := JSP452Audit.StarHost.matchingInColour M (G \ eraseInternal G P)
  let J := JSP452Audit.StarHost.matchingInColour M (G \ eraseInternal G (P∪A))
  let E := T\L.verts
  have inT : L.verts⊆T := by
    rintro v ⟨w,me,edge⟩
    exact ⟨((in_internal_colour G P v w).mp edge).2.1,M.edge_vert me⟩
  have internal : L.verts.ncard≤2*matchingEdges (G.induce P) := by
    have m := JSP452Audit.StarHost.matchingInColour_matching M hm (G \ eraseInternal G P)
    have paired := matching_vertices_eq_twice_edges m
    have bound := le_matchingEdges m
    rw [rank_of_internal_edges] at bound
    change L.verts.ncard=2*L.edgeSet.ncard at paired
    change L.edgeSet.ncard≤matchingEdges (G.induce P) at bound
    omega
  have outer (v:E) : ∃w∈A,M.Adj v.val w := by
    obtain ⟨w,e,_⟩ := hm v.property.1.2
    have wp : w∉P := fun hp => v.property.2 (show v.val∈L.verts from
      ⟨w,e,(in_internal_colour G P _ _).mpr ⟨M.adj_sub e,v.property.1.1,hp⟩⟩)
    exact ⟨w,outside _ v.property.1.1 w (M.adj_sub e) wp,e⟩
  let f (v:E) := (outer v).choose
  have roots (v:E) : f v∈A := (outer v).choose_spec.1
  have adj (v:E) : M.Adj v.val (f v) := (outer v).choose_spec.2
  have inj : Function.Injective f := by
    intro v w eq
    apply Subtype.ext
    exact hm.eq_of_adj_left (adj v).symm (eq.symm ▸ (adj w).symm)
  let B := Set.range f
  have bSize : B.ncard=E.ncard := (Set.ncard_range_of_injective inj).trans (Nat.card_coe_set_eq _)
  have ba : B⊆A := by rintro _ ⟨v,rfl⟩;exact roots v
  have extCap := Set.ncard_le_ncard ba
  have diff := Set.ncard_sdiff_add_ncard_of_subset inT
  change E.ncard+L.verts.ncard=T.ncard at diff
  have tj (v:X) (hv:v∈T) : v∈J.verts := by
    obtain ⟨w,e,_⟩ := hm hv.2
    have wIn : w∈P∪A := by
      by_cases wp:w∈P
      · exact Or.inl wp
      · exact Or.inr (outside v hv.1 w (M.adj_sub e) wp)
    exact ⟨w,e,(in_internal_colour G (P∪A) v w).mpr ⟨M.adj_sub e,Or.inl hv.1,wIn⟩⟩
  have bj : B⊆J.verts := by
    rintro _ ⟨v,rfl⟩
    exact ⟨v.val,(adj v).symm,(in_internal_colour G (P∪A) _ _).mpr
      ⟨(M.adj_sub (adj v)).symm,Or.inr (roots v),Or.inl v.property.1.1⟩⟩
  have dis : Disjoint T B := apart.mono Set.inter_subset_left ba
  have bound := Set.ncard_le_ncard (Set.union_subset tj bj)
  rw [Set.ncard_union_eq dis,bSize] at bound
  have jm := JSP452Audit.StarHost.matchingInColour_matching M hm (G \ eraseInternal G (P∪A))
  have paired := matching_vertices_eq_twice_edges jm
  have limited := le_matchingEdges jm
  rw [rank_of_internal_edges] at limited
  change J.verts.ncard=2*J.edgeSet.ncard at paired
  change J.edgeSet.ncard≤matchingEdges (G.induce (P∪A)) at limited
  omega

#print axioms protected_matching_counts
end JSP452Audit.StarHost
