import CanonicalCut
import TutteBergeExact

namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Genuine optimality of a canonical cut at the matching deficiency. -/
theorem Spec.match_gap_canonical :
    ∃ S T : Set V, Disjoint S T ∧
      retainedScore P.graph (P.canonicalKept S T) = Nat.card P.Vertex + minUnmatched P.graph := by
  classical
  obtain ⟨S,T,dis,best⟩ := P.canonical_max_score
  obtain ⟨bound,⟨W,attain⟩⟩ := max_retainedScore_exact P.graph
  exact ⟨S,T,dis,le_antisymm (bound _) (attain ▸ best W)⟩

/-- A useful rejection test for a proposed upper bound on the original total
    two-color cap error. It suffices to prove it for just one parity choice
    on all the disjoint, canonical two-set cuts of that graph. -/
theorem Spec.color_gap_of_cut_bounds (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v)
    (b : Bool) (K : ℕ)
    (cuts : ∀ S T : Set V, Disjoint S T →
      retainedScore (P.withPoolBit b).graph ((P.withPoolBit b).canonicalKept S T) ≤
        Nat.card (P.withPoolBit b).Vertex + K) : P.minColorGap ≤ K := by
  let Q := P.withPoolBit b
  obtain ⟨S,T,dis,exactCut⟩ := Q.match_gap_canonical
  have bound := cuts S T dis
  change retainedScore Q.graph (Q.canonicalKept S T) ≤ Nat.card Q.Vertex + K at bound
  rw [exactCut] at bound
  have one := Q.minColorGap_le_graphGap caps
  change P.minColorGap ≤ minUnmatched Q.graph at one
  omega

#print axioms Spec.match_gap_canonical
#print axioms Spec.color_gap_of_cut_bounds
end JSP452Audit.Padded
