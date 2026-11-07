import SmallLocalPotential

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A degree-bounded coloring whenever a matching covers the full-degree vertices. -/
def MatchingCoverDegreeSplit {X : Type*} (G : SimpleGraph X) : Prop :=
  ∀ p q : ℕ, 1 ≤ p → 1 ≤ q →
    (∀ v, Nat.card (G.neighborSet v) ≤ p + q) →
    (∃ M : G.Subgraph, M.IsMatching ∧ ∀ v, Nat.card (G.neighborSet v) = p + q → v ∈ M.verts) →
    ∃ R : SimpleGraph X, R ≤ G ∧ ∀ v,
      Nat.card (R.neighborSet v) ≤ p ∧ Nat.card ((G \ R).neighborSet v) ≤ q

/-- For a vertex missed by an actual maximum matching, the potential loss is exactly its degree. -/
theorem potential_equal_charge_of_avoiding {X : Type*} [Finite X] (G : SimpleGraph X) (v : X)
    (avoid : ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧ v ∉ M.verts) :
    Nat.card (G.neighborSet v) + edgePotential (G.induce {x | x ≠ v}) = edgePotential G := by
  have keep := matchingEdges_delete_eq_of_avoiding G v avoid
  have edges := card_neighbor_add_induce_edge_ncard G v
  have before := potential_plus_matching G
  have after := potential_plus_matching (G.induce {x | x ≠ v})
  omega

/-- The degree split on this particular host suffices for the one-star potential step. -/
theorem local_potential_of_degree_split {X : Type*} [Finite X] (G : SimpleGraph X)
    (split : MatchingCoverDegreeSplit G) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (forced : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, (a+b-2) + edgePotential (G.induce {x | x ≠ v}) ≤ edgePotential G := by
  by_cases small : a ≤ 2 ∨ b ≤ 2
  · exact local_potential_small G ha hb small forced
  let p := a-1
  let q := b-1
  have pa : 1 ≤ p := by dsimp [p]; omega
  have qb : 1 ≤ q := by dsimp [q]; omega
  have sum : p+q = a+b-2 := by dsimp [p,q]; omega
  by_cases high : ∃ v, p+q < Nat.card (G.neighborSet v)
  · obtain ⟨v,hv⟩ := high
    have paid := degree_potential_charge G v
    exact ⟨v,by omega⟩
  have bound (v : X) : Nat.card (G.neighborSet v) ≤ p+q :=
    Nat.le_of_not_gt fun h => high ⟨v,h⟩
  obtain ⟨M,hM,maximum⟩ := exists_maximum_matching G
  by_cases covered : ∀ v, Nat.card (G.neighborSet v) = p+q → v ∈ M.verts
  · obtain ⟨R,sub,degs⟩ := split p q pa qb bound ⟨M,hM,covered⟩
    rcases forced R sub with red | blue
    · obtain ⟨v,hv⟩ := high_degree_of_star red
      have cap := (degs v).1
      change Nat.card (R.neighborSet v) ≤ a-1 at cap
      omega
    · obtain ⟨v,hv⟩ := high_degree_of_star blue
      have cap := (degs v).2
      change Nat.card ((G \ R).neighborSet v) ≤ b-1 at cap
      omega
  · push Not at covered
    obtain ⟨v,tight,miss⟩ := covered
    have paid := potential_equal_charge_of_avoiding G v ⟨M,hM,maximum,miss⟩
    exact ⟨v,by omega⟩

#print axioms potential_equal_charge_of_avoiding
#print axioms local_potential_of_degree_split
end JSP452Audit.StarHost
