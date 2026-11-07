import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost

open SimpleGraph

/-- Color exactly k of the undirected edges of F red; the blue graph is the relative complement. -/
theorem exists_edge_split {X : Type*} [Finite X] (F : SimpleGraph X) (k : ℕ)
    (hk : k ≤ F.edgeSet.ncard) :
    ∃ R : SimpleGraph X, R ≤ F ∧ R.edgeSet.ncard = k ∧
      (F \ R).edgeSet.ncard = F.edgeSet.ncard - k := by
  obtain ⟨s, sub, card⟩ := Set.exists_subset_card_eq hk
  have noDiag : Disjoint s Sym2.diagSet :=
    Set.disjoint_left.mpr fun _ he hd => F.edgeSet_subset_compl_diagSet (sub he) hd
  have edges : (fromEdgeSet s).edgeSet = s := by
    rw [edgeSet_fromEdgeSet, noDiag.sdiff_eq_left]
  refine ⟨fromEdgeSet s, edgeSet_subset_edgeSet.mp (by rwa [edges]), ?_, ?_⟩
  · rw [edges, card]
  · rw [edgeSet_sdiff, edges, Set.ncard_sdiff' sub, card]

#print axioms exists_edge_split
end JSP452Audit.StarHost
