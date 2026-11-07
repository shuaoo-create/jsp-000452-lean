import GraphMatchBarrier
import MatchingOptimization
import PairFamily
import ExtremaBoundary

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

theorem uncovered_eq {X : Type*} [Finite X] {G : SimpleGraph X} {M : G.Subgraph} (h : M.IsMatching) :
    Nat.card {x : X // x ∉ M.verts} = Nat.card X - 2*M.edgeSet.ncard := by
  change Nat.card ↥(M.vertsᶜ) = _
  rw [Nat.card_coe_set_eq,Set.ncard_compl,matching_vertices_eq_twice_edges h]

theorem minUnmatched_eq_deficit {X : Type*} [Finite X] (G : SimpleGraph X) :
    minUnmatched G = Nat.card X - 2*matchingEdges G := by
  obtain ⟨M,matchM,maxEq⟩ := exists_maximum_matching G
  let choices : Set ℕ := {n | ∃ N : G.Subgraph, N.IsMatching ∧ Nat.card {x // x ∉ N.verts}=n}
  have attained : (Nat.card X-2*matchingEdges G) ∈ choices :=
    ⟨M,matchM,(uncovered_eq matchM).trans (by rw [maxEq])⟩
  change sInf choices = _
  apply Nat.le_antisymm (Nat.sInf_le attained)
  obtain ⟨N,matchN,eq⟩ := (Nat.sInf_mem (s := choices) ⟨_,attained⟩)
  have bound := le_matchingEdges matchN
  rw [← eq,uncovered_eq matchN]
  omega

/-- Match every old uncovered vertex to a different new vertex, using no
    additional hypotheses about the original graph. -/
theorem join_perfect_at_deficit {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ N : (tutteJoin G (minUnmatched G)).Subgraph, N.IsPerfectMatching := by
  classical
  let _ := Fintype.ofFinite X
  obtain ⟨M,hM,eq⟩ := exists_maximum_matching G
  let d := minUnmatched G
  let H := tutteJoin G d
  let B := {x : X // x ∉ M.verts}
  have bsize : Nat.card B = d := by
    dsimp only [d]; rw [minUnmatched_eq_deficit]; exact (uncovered_eq hM).trans (by rw [eq])
  let e : B ≃ Fin d := Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm.trans bsize)
  let l : B ↪ X ⊕ Fin d := (Function.Embedding.subtype _).trans Function.Embedding.inl
  let r : B ↪ X ⊕ Fin d := e.toEmbedding.trans Function.Embedding.inr
  let ins : G →g H := ⟨Sum.inl,fun h => h⟩
  have edge (b : B) : H.Adj (l b) (r b) := trivial
  have sep : Disjoint (Set.range l) (Set.range r) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨a,rfl⟩ ⟨b,eq⟩
    cases eq
  let newPairs := pairFamily H l r edge
  have dis : Disjoint (M.map ins).verts newPairs.verts := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨v,used,rfl⟩ (⟨a,ha⟩ | ⟨b,hb⟩)
    · have same : a.val = v := Sum.inl.inj ha
      exact a.property (same ▸ used)
    · cases hb
  refine ⟨M.map ins ⊔ newPairs,matching_sup_of_disjoint_verts H (hM.map ins Sum.inl_injective)
    (pairFamily_isMatching H l r edge sep) dis,?_⟩
  rintro (v | i)
  · by_cases used : v ∈ M.verts
    · exact Or.inl ⟨v,used,rfl⟩
    · exact Or.inr (Or.inl ⟨⟨v,used⟩,rfl⟩)
  · exact Or.inr (Or.inr ⟨e.symm i,congrArg Sum.inr (e.apply_symm_apply i)⟩)

#print axioms minUnmatched_eq_deficit
#print axioms join_perfect_at_deficit
end JSP452Audit.StarHost
