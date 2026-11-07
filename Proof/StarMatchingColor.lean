import SelectCenter
import Mathlib.Combinatorics.SimpleGraph.Matching

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Extending the edge relation of a matching to the whole ambient vertex
    type gives at most one neighbor at every vertex, including unused ones. -/
theorem spanningMatching_degree_le_one {X : Type*} {G : SimpleGraph X}
    (M : G.Subgraph) (hM : M.IsMatching) (v : X) :
    Nat.card (M.spanningCoe.neighborSet v) ≤ 1 := by
  let f (_ : M.spanningCoe.neighborSet v) := (0 : Fin 1)
  have inj : Function.Injective f := by
    intro i j _
    exact Subtype.ext (hM.eq_of_adj_left i.property j.property)
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f inj

theorem no_large_star_in_spanningMatching {X : Type*} [Finite X] {G : SimpleGraph X}
    (M : G.Subgraph) (hM : M.IsMatching) {a : ℕ} (ha : 2 ≤ a) :
    ¬ (oneStar a).IsContained M.spanningCoe := by
  intro h
  obtain ⟨v,hv⟩ := high_degree_of_star h
  have bound := spanningMatching_degree_le_one M hM v
  omega

/-- This specific red matching coloring must give a blue star; the indicated
    center is measured in its actual blue complement, not just in G. -/
theorem blue_center_of_matching_coloring {X : Type*} [Finite X] {G : SimpleGraph X}
    (M : G.Subgraph) (hM : M.IsMatching) {a b : ℕ} (ha : 2 ≤ a)
    (forced : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, b ≤ Nat.card ((G \ M.spanningCoe).neighborSet v) := by
  rcases forced M.spanningCoe M.spanningCoe_le with red | blue
  · exact (no_large_star_in_spanningMatching M hM ha red).elim
  · exact high_degree_of_star blue

#print axioms spanningMatching_degree_le_one
#print axioms no_large_star_in_spanningMatching
#print axioms blue_center_of_matching_coloring
end JSP452Audit.StarHost
