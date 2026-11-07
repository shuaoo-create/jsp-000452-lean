import OriginalCutScore
import CanonicalSurplus
import ParityGap
namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost
variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

theorem Spec.canonical_sandwich {S T : Set V} (dis : Disjoint S T)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.cutDeficit S T ≤ P.canonicalSurplus S T ∧ P.canonicalSurplus S T ≤ P.cutDeficit S T + 1 := by
  have lo := P.singleton_tightOdd_le_odd dis
  have hi := P.odd_canonical_upper dis
  rw [P.cutDeficit_eq_canonical S T caps]
  unfold Spec.canonicalSurplus Spec.removedSize
  omega

/-- Every original cut supplies a lower bound for the red-blue degree error. -/
theorem Spec.cutDeficit_le_minColorGap {S T : Set V} (dis : Disjoint S T)
    (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    P.cutDeficit S T ≤ (P.minColorGap : ℤ) := by
  have leBit (b : Bool) : P.cutDeficit S T ≤ (minUnmatched (P.withPoolBit b).graph : ℤ) := by
    let Q := P.withPoolBit b
    exact ((Q.canonical_sandwich dis caps).1).trans (Q.canonicalSurplus_le S T)
  have l := leBit false
  have r := leBit true
  rw [P.minColorGap_eq_matching caps]
  omega

/-- An original, disjoint pair attains the exact minimum; the two auxiliary
    parities eliminate the possible one-unit slack of the optional pool. -/
theorem Spec.exact_factor_deficiency (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    (∀ S T : Set V, Disjoint S T → P.cutDeficit S T ≤ (P.minColorGap : ℤ)) ∧
      ∃ S T : Set V, Disjoint S T ∧ P.cutDeficit S T = (P.minColorGap : ℤ) := by
  refine ⟨fun _ _ h => P.cutDeficit_le_minColorGap h caps,?_⟩
  obtain ⟨b,strict⟩ := P.exists_poolBit_strict_gap caps
  let Q := P.withPoolBit b
  obtain ⟨S,T,dis,att⟩ := Q.canonicalSurplus_attained
  have hi := (Q.canonical_sandwich dis caps).2
  have low := P.cutDeficit_le_minColorGap dis caps
  change P.minColorGap < minUnmatched Q.graph at strict
  change Q.canonicalSurplus S T ≤ P.cutDeficit S T + 1 at hi
  exact ⟨S,T,dis,by omega⟩

/-- A witness on each side of the min-max identity, on the same original host. -/
theorem Spec.factor_witnesses (caps : ∀ v, P.G.degree v ≤ P.A v + P.B v) :
    ∃ (F : SimpleGraph V) (S T : Set V), F ≤ P.G ∧ Disjoint S T ∧
      (P.colorGap F : ℤ) = P.cutDeficit S T ∧
      (∀ F' : SimpleGraph V, F' ≤ P.G → P.colorGap F ≤ P.colorGap F') ∧
      (∀ S' T' : Set V, Disjoint S' T' → P.cutDeficit S' T' ≤ P.cutDeficit S T) := by
  let costs : Set ℕ := {n | ∃ F : SimpleGraph V, F ≤ P.G ∧ P.colorGap F=n}
  have someCost : costs.Nonempty := ⟨_,⊥,bot_le,rfl⟩
  obtain ⟨F,sub,cost⟩ := Nat.sInf_mem (s := costs) someCost
  change P.colorGap F=P.minColorGap at cost
  obtain ⟨bounds,S,T,dis,eq⟩ := P.exact_factor_deficiency caps
  refine ⟨F,S,T,sub,dis,by omega,?_,?_⟩
  · intro F' incl
    rw [cost]
    exact Nat.sInf_le (show P.colorGap F' ∈ costs from ⟨F',incl,rfl⟩)
  · intro S' T' dd
    rw [eq]
    exact bounds _ _ dd

#print axioms Spec.exact_factor_deficiency
#print axioms Spec.factor_witnesses
end JSP452Audit.Padded
