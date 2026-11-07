import CoverToMaximum
import DeletionStep

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
/-- A vertex of degree D has to be used by the matching when its complement
has maximum degree at most D-1. -/
theorem full_covered_of_matching_remainder (G : SimpleGraph X) (M : G.Subgraph) (D : ℕ)
    (pos : 0 < D) (cap : ∀ x, Nat.card ((G \ M.spanningCoe).neighborSet x) ≤ D-1)
    {x : X} (full : Nat.card (G.neighborSet x) = D) : x ∈ M.verts := by
  by_contra miss
  have equal : (G \ M.spanningCoe).neighborSet x = G.neighborSet x := by
    ext y
    constructor
    · exact fun h => h.1
    · intro edge
      exact ⟨edge,fun red => miss (M.edge_vert red)⟩
  have h := cap x
  rw [equal,full] at h
  omega

theorem deletionBudget_zero_iff_minimumExposure_zero (G : SimpleGraph X) (D : ℕ)
    (pos : 0 < D) (bound : ∀ x, Nat.card (G.neighborSet x) ≤ D) :
    deletionBudget G D = 0 ↔ minimumExposure G D = 0 := by
  constructor
  · intro noCost
    obtain ⟨U,good,attained⟩ := deletionBudget_attained G D
    have empty : U = ∅ := (Set.ncard_eq_zero (Set.toFinite U)).mp (attained.trans noCost)
    subst U
    let inclusion : G ↪g G.induce (∅ : Set X)ᶜ := {
      toFun := fun x => ⟨x,fun h => h⟩
      inj' := fun _ _ eq => congrArg (fun z : ↥((∅ : Set X)ᶜ) => z.val) eq
      map_rel_iff' := Iff.rfl }
    obtain ⟨M,hm,cap⟩ := admits_remainder_of_induced_embedding inclusion good
    obtain ⟨N,hn,largest,covered⟩ := exists_maximum_matching_covering G M hm
    have empty : exposedFull G N D = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro v hit
      exact hit.1 (covered (full_covered_of_matching_remainder G M D pos cap hit.2))
    have good := minimumExposure_le G D N hn largest
    rw [empty,Set.ncard_empty] at good
    exact Nat.eq_zero_of_le_zero good
  · intro noExposure
    have good := deletionBudget_le_minimumExposure G D pos bound
    rw [noExposure] at good
    exact Nat.eq_zero_of_le_zero good

#print axioms full_covered_of_matching_remainder
#print axioms deletionBudget_zero_iff_minimumExposure_zero
end JSP452Audit.StarHost
