import MatchDualJoin

namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost

/-- Every maximum matching certifies the exact parity of the minimum uncovered count. -/
theorem minUnmatched_add_twice_matching {X : Type*} [Finite X] (G : SimpleGraph X) :
    minUnmatched G + 2 * matchingEdges G = Nat.card X := by
  obtain ⟨M,hm,hM⟩ := exists_maximum_matching G
  have bound := Set.ncard_le_ncard (Set.subset_univ M.verts)
  rw [Set.ncard_univ,matching_vertices_eq_twice_edges hm,hM] at bound
  rw [minUnmatched_eq_deficit]
  omega

theorem minUnmatched_mod_two {X : Type*} [Finite X] (G : SimpleGraph X) :
    minUnmatched G % 2 = Nat.card X % 2 := by
  have := minUnmatched_add_twice_matching G
  omega

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Flipping the pool bit adds exactly one global vertex. -/
theorem Spec.poolBit_true_card :
    Nat.card (P.withPoolBit true).Vertex = Nat.card (P.withPoolBit false).Vertex + 1 := by
  change Nat.card (P.Stub ⊕ ((P.Mandatory ⊕ P.Optional) ⊕ Fin 1)) =
    Nat.card (P.Stub ⊕ ((P.Mandatory ⊕ P.Optional) ⊕ Fin 0)) + 1
  simp only [Nat.card_sum,Nat.card_fin]; omega

theorem Spec.poolBit_gap_opposite_mod :
    minUnmatched (P.withPoolBit true).graph % 2 ≠ minUnmatched (P.withPoolBit false).graph % 2 := by
  rw [minUnmatched_mod_two, minUnmatched_mod_two, P.poolBit_true_card]
  omega

theorem Spec.minColorGap_le_each_bit (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) (b : Bool) :
    P.minColorGap ≤ minUnmatched (P.withPoolBit b).graph := by
  rw [P.minColorGap_eq_matching caps]
  cases b
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem Spec.exists_poolBit_strict_gap (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    ∃ b : Bool, P.minColorGap < minUnmatched (P.withPoolBit b).graph := by
  have ne := P.poolBit_gap_opposite_mod
  have l := P.minColorGap_le_each_bit caps false
  have r := P.minColorGap_le_each_bit caps true
  by_cases strict : P.minColorGap < minUnmatched (P.withPoolBit false).graph
  · exact ⟨false,strict⟩
  · exact ⟨true,by omega⟩

#print axioms minUnmatched_add_twice_matching
#print axioms Spec.poolBit_true_card
#print axioms Spec.poolBit_gap_opposite_mod
#print axioms Spec.minColorGap_le_each_bit
#print axioms Spec.exists_poolBit_strict_gap
end JSP452Audit.Padded
