import ExposeRestrict

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- The attainable numbers of degree-D vertices missed by genuine maximum matchings. -/
def maximumExposureCounts (G : SimpleGraph X) (D : ℕ) : Set ℕ :=
  {n | ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
    (exposedFull G M D).ncard = n}

/-- Liu's degree-D exposure parameter, minimized only over maximum matchings. -/
noncomputable def minimumExposure (G : SimpleGraph X) (D : ℕ) : ℕ :=
  sInf (maximumExposureCounts G D)

private theorem maximumExposureCounts_nonempty (G : SimpleGraph X) (D : ℕ) :
    (maximumExposureCounts G D).Nonempty := by
  obtain ⟨M,hm,maximum⟩ := exists_maximum_matching G
  exact ⟨_,M,hm,maximum,rfl⟩

theorem minimumExposure_attained (G : SimpleGraph X) (D : ℕ) :
    ∃ M : G.Subgraph, M.IsMatching ∧ M.edgeSet.ncard = matchingEdges G ∧
      (exposedFull G M D).ncard = minimumExposure G D :=
  Nat.sInf_mem (maximumExposureCounts_nonempty G D)

omit [Finite X] in
theorem minimumExposure_le (G : SimpleGraph X) (D : ℕ) (M : G.Subgraph)
    (hm : M.IsMatching) (maximum : M.edgeSet.ncard = matchingEdges G) :
    minimumExposure G D ≤ (exposedFull G M D).ncard :=
  Nat.sInf_le (show (exposedFull G M D).ncard ∈ maximumExposureCounts G D from ⟨M,hm,maximum,rfl⟩)

theorem le_minimumExposure_iff (G : SimpleGraph X) (D k : ℕ) :
    k ≤ minimumExposure G D ↔
      ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard = matchingEdges G →
        k ≤ (exposedFull G M D).ncard := by
  constructor
  · intro low M hm maximum
    exact low.trans (minimumExposure_le G D M hm maximum)
  · intro low
    obtain ⟨M,hm,maximum,attained⟩ := minimumExposure_attained G D
    exact (low M hm maximum).trans_eq attained

#print axioms minimumExposure_attained
#print axioms minimumExposure_le
#print axioms le_minimumExposure_iff
end JSP452Audit.StarHost
