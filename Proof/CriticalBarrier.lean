import ResidualBarrier
import LocalOddReplacement
import OddLocalCritical
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- Every residual component at a largest tight barrier actually has odd order,
and deleting any one of its labeled vertices leaves a perfect matching there. -/
theorem largest_barrier_components {X : Type*} [Finite X] (G : SimpleGraph X)
    (S : Set X) (tight : IsTightBarrier G S)
    (maximal : ∀ A : Set X, IsTightBarrier G A → A.ncard≤S.ncard)
    (c : (G.induce Sᶜ).ConnectedComponent) :
    Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp) := by
  classical
  let Y := G.induce Sᶜ
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  apply odd_critical_of_strict_nonempty_cuts
  intro Z hz
  let U : Set ↥(Sᶜ : Set X) := Subtype.val '' Z
  have nonempty : U.Nonempty := hz.image _
  have ncard : U.ncard=Z.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have strict := largest_barrier_residual_strict G S tight maximal U nonempty
  have replace := odd_components_replace_component Y c Z
  change (Y.induce Uᶜ).oddComponents.ncard < Y.oddComponents.ncard + U.ncard at strict
  change (Y.induce Uᶜ).oddComponents.ncard + _ = Y.oddComponents.ncard + _ at replace
  change ((Y.induce c.supp).induce Zᶜ).oddComponents.ncard < (if Odd (Nat.card c.supp) then 1 else 0) + Z.ncard
  omega

theorem exists_critical_barrier {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ S, IsTightBarrier G S ∧
      ∀ c : (G.induce Sᶜ).ConnectedComponent,
        Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp) := by
  obtain ⟨S,tight,largest⟩ := exists_largest_tight_barrier G
  exact ⟨S,tight,largest_barrier_components G S tight largest⟩
#print axioms largest_barrier_components
#print axioms exists_critical_barrier
end JSP452Audit.StarHost