import ComponentDeletionBudget
import ReserveRowBudget
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph

theorem edge_ncard_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) :
    (G ⊕g H).edgeSet.ncard = G.edgeSet.ncard + H.edgeSet.ncard :=
  (Nat.card_congr (edgeSetSumEquiv (G := G) (H := H))).trans Nat.card_sum

private theorem matching_comap_closed {X Y : Type*} {G : SimpleGraph X} {J : SimpleGraph Y}
    (e : G ↪g J) {M : J.Subgraph} (hM : M.IsMatching)
    (closed : ∀ x y, J.Adj (e x) y → ∃ z, e z = y) : (M.comap e.toHom).IsMatching := by
  intro x hx
  obtain ⟨y,edge,unique⟩ := hM hx
  obtain ⟨z,rfl⟩ := closed x y (M.adj_sub edge)
  exact ⟨z,⟨e.map_rel_iff.mp (M.adj_sub edge),edge⟩,
    fun w ew => e.injective (unique (e w) ew.2)⟩

theorem matchingEdges_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) :
    matchingEdges (G ⊕g H) = matchingEdges G + matchingEdges H := by
  let l : G ↪g G ⊕g H := Embedding.sumInl
  let r : H ↪g G ⊕g H := Embedding.sumInr
  apply le_antisymm
  · obtain ⟨M,matchM,maxM⟩ := exists_maximum_matching (G ⊕g H)
    have lm := matching_comap_closed l matchM (by
      rintro x (y|y) adj
      · exact ⟨y,rfl⟩
      · exact False.elim (SimpleGraph.not_adj_sum_inl_inr x y adj))
    have rm := matching_comap_closed r matchM (by
      rintro x (y|y) adj
      · exact False.elim (SimpleGraph.not_adj_sum_inl_inr y x adj.symm)
      · exact ⟨y,rfl⟩)
    have verts : M.verts.ncard = (M.comap l.toHom).verts.ncard + (M.comap r.toHom).verts.ncard :=
      (Nat.card_congr (Equiv.subtypeSum (p := fun z => z ∈ M.verts))).trans Nat.card_sum
    rw [matching_vertices_eq_twice_edges matchM, maxM, matching_vertices_eq_twice_edges lm,
      matching_vertices_eq_twice_edges rm] at verts
    have left := le_matchingEdges lm
    have right := le_matchingEdges rm
    omega
  · obtain ⟨M,hm,maxM⟩ := exists_maximum_matching G
    obtain ⟨N,hn,maxN⟩ := exists_maximum_matching H
    let L := M.map l.toHom
    let R := N.map r.toHom
    have apart : Disjoint L.verts R.verts := by
      apply Set.disjoint_left.mpr
      rintro _ ⟨x,_,rfl⟩ ⟨y,_,same⟩
      change (Sum.inr y : X ⊕ Y) = Sum.inl x at same
      contradiction
    have merged := Padded.matching_sup_of_disjoint_verts (G ⊕g H)
      (hm.map l.toHom l.injective) (hn.map r.toHom r.injective) apart
    have count : (L ⊔ R).verts.ncard = M.verts.ncard + N.verts.ncard := by
      change (L.verts ∪ R.verts).ncard = _
      rw [Set.ncard_union_eq apart]
      rw [show L.verts = l '' M.verts from rfl,show R.verts = r '' N.verts from rfl,
        Set.ncard_image_of_injective _ l.injective,Set.ncard_image_of_injective _ r.injective]
    rw [matching_vertices_eq_twice_edges merged,matching_vertices_eq_twice_edges hm,
      matching_vertices_eq_twice_edges hn,maxM,maxN] at count
    have upper := le_matchingEdges merged
    omega

theorem baseReserve_sumGraph {X Y : Type*} [Finite X] [Finite Y]
    (G : SimpleGraph X) (H : SimpleGraph Y) (k : ℕ) :
    baseReserve (G ⊕g H) k = baseReserve G k + baseReserve H k := by
  have total := base_reserve_account (G ⊕g H) k
  have left := base_reserve_account G k
  have right := base_reserve_account H k
  simp only [matchingEdges_sumGraph, deletionBudget_sumGraph, Finset.sum_add_distrib,
    edge_ncard_sumGraph] at total
  omega

#print axioms matchingEdges_sumGraph
#print axioms baseReserve_sumGraph
end JSP452Audit.StarHost
