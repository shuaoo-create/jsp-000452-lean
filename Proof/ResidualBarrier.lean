import NestedBarrier
import MaximalBarrier
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

theorem largest_barrier_residual_strict {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S) (maximal : ∀ A : Set X, IsTightBarrier G A → A.ncard≤S.ncard)
    (Z : Set ↥(Sᶜ : Set X)) (present : Z.Nonempty) :
    ((G.induce Sᶜ).induce Zᶜ).oddComponents.ncard < (G.induce Sᶜ).oddComponents.ncard + Z.ncard := by
  have less := strict_of_strict_superset_largest_tight G S (outerCut S Z) maximal (outerCut_strict S Z present)
  have iso := odd_ncard_iso (nestedCutIso G S Z)
  rw [outerCut_ncard] at less
  change (G.induce Sᶜ).oddComponents.ncard = S.ncard + minUnmatched G at tight
  omega
#print axioms largest_barrier_residual_strict
end JSP452Audit.StarHost