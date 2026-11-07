import FactorDualCut
import OddLower
import OddUpper

namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

noncomputable def Spec.removedSize (S T : Set V) : ℕ := Nat.card {z : P.Vertex // ¬P.keptBy S T z}

theorem Spec.kept_plus_removed (S T : Set V) :
    (P.canonicalKept S T).card + P.removedSize S T = Nat.card P.Vertex := by
  classical
  let keep (z : P.Vertex) := P.keptBy S T z
  have part := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P.Vertex)) keep
  unfold Spec.canonicalKept Spec.removedSize
  rw [Nat.card_eq_fintype_card (α := {z : P.Vertex // ¬P.keptBy S T z}),Fintype.card_subtype,
    Nat.card_eq_fintype_card]
  simpa [keep] using part

/-- Signed score of the actual canonical cut, not of a proxy graph. -/
noncomputable def Spec.canonicalSurplus (S T : Set V) : ℤ :=
  ((P.canonGraph S T).oddComponents.ncard : ℤ) - (P.removedSize S T : ℤ)

theorem Spec.canonicalSurplus_le (S T : Set V) :
    P.canonicalSurplus S T ≤ (minUnmatched P.graph : ℤ) := by
  classical
  have bound := (max_retainedScore_exact P.graph).1 (P.canonicalKept S T)
  change (P.canonGraph S T).oddComponents.ncard + (P.canonicalKept S T).card ≤ _ at bound
  have total := P.kept_plus_removed S T
  unfold Spec.canonicalSurplus
  omega

theorem Spec.canonicalSurplus_attained :
    ∃ S T : Set V, Disjoint S T ∧ P.canonicalSurplus S T = (minUnmatched P.graph : ℤ) := by
  obtain ⟨S,T,dis,eq⟩ := P.match_gap_canonical
  refine ⟨S,T,dis,?_⟩
  change (P.canonGraph S T).oddComponents.ncard + (P.canonicalKept S T).card = _ at eq
  have total := P.kept_plus_removed S T
  unfold Spec.canonicalSurplus
  omega

#print axioms Spec.canonicalSurplus_attained
end JSP452Audit.Padded
