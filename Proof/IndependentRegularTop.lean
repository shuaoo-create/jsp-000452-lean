import RegularCriticalHost
import ZeroBudgetExposure
import ComponentZeroReserve

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- In a nonempty regular factor-critical graph exactly one deletion is
needed at its positive degree ceiling. -/
theorem regular_factorCritical_top_budget_one [Nonempty X] (Q : SimpleGraph X) (D : ℕ)
    (pos : 0 < D) (reg : ∀ x, Nat.card (Q.neighborSet x) = D)
    (crit : PerfectAfterEveryDeletion Q) : deletionBudget Q D = 1 := by
  classical
  let v := Classical.arbitrary X
  have exposure := regular_factorCritical_exposure Q crit v D reg
  have cap (x : X) := (reg x).le
  have upper := deletionBudget_le_minimumExposure Q D pos cap
  have zero := deletionBudget_zero_iff_minimumExposure_zero Q D pos cap
  omega

/-- A perfect matching covers every full-degree vertex, so the entire
original graph admits the required partition at zero deletion cost. -/
theorem top_budget_zero_of_perfect {Y : Type*} [Finite Y] (H : SimpleGraph Y) (D : ℕ)
    (pos : 0 < D) (cap : ∀ y, Nat.card (H.neighborSet y) ≤ D)
    (perfect : ∃ M : H.Subgraph, M.IsPerfectMatching) : deletionBudget H D = 0 := by
  obtain ⟨M,hm⟩ := perfect
  have good := admits_remainder_of_full_cover H D pos cap M hm.1 (fun y _ => hm.2 y)
  have empty : admits_matching_remainder (H.induce (∅ : Set Y)ᶜ) D := by
    rw [Set.compl_empty]
    exact admits_remainder_of_induced_embedding (induceUnivIso H).toEmbedding good
  have upper := deletionBudget_le_of_witness H D ∅ empty
  simpa only [Set.ncard_empty,Nat.le_zero] using upper

/-- Once one vertex has been removed, every further induced deletion also
has zero top budget. Independence of I and regularity are unnecessary. -/
theorem factorCritical_top_budget_after_nonempty_cut (Q : SimpleGraph X) (D : ℕ)
    (pos : 0 < D) (cap : ∀ v, Nat.card (Q.neighborSet v) ≤ D)
    (crit : PerfectAfterEveryDeletion Q) (I : Set X) (present : I.Nonempty) :
    deletionBudget (Q.induce Iᶜ) D = 0 := by
  obtain ⟨v,hv⟩ := present
  let H := Q.induce {x | x ≠ v}
  have perfect := crit v
  have bound (x : {x : X // x ≠ v}) : Nat.card (H.neighborSet x) ≤ D :=
    (induced_neighbor_count_le Q _ x).trans (cap _)
  have zero := top_budget_zero_of_perfect H D pos bound perfect
  let e : Q.induce Iᶜ ↪g H := {
    toFun := fun x => ⟨x.val,fun eq => x.property (eq ▸ hv)⟩
    inj' := fun _ _ h => Subtype.ext (congrArg (fun w : {x : X // x ≠ v} => w.val) h)
    map_rel_iff' := Iff.rfl }
  exact Nat.eq_zero_of_le_zero ((deletionBudget_mono_embedding e D).trans_eq zero)

#print axioms regular_factorCritical_top_budget_one
#print axioms top_budget_zero_of_perfect
#print axioms factorCritical_top_budget_after_nonempty_cut
end JSP452Audit.StarHost
