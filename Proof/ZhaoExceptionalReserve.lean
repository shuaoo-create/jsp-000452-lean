import UnpaidRegularStructure
import ZhaoFamilyCritical
import ZhaoFourCritical
namespace JSP452Audit.StarHost
open SimpleGraph
theorem zhao_family_reserve (d k : ℕ) (hd : 2≤d) :
    2*d-2 ≤ baseReserve (zhaoGraph d) k := by
  exact (zhao_family_base_given_critical d hd (zhao_factor_critical d hd)).trans
    (baseReserve_le_truncation _ (2*d) k (fun x => (zhao_regular d x).le))

theorem zhao_four_complement_reserve (k : ℕ) : 1≤baseReserve (zhaoGraph 2)ᶜ k := by
  exact (zhao_four_complement_base_given_critical zhao_four_complement_critical).trans
    (baseReserve_le_truncation _ 4 k (fun x => (zhao_four_complement_certificate.1 x).le))

/-- Real costs exclude all the listed exceptional models up to relabeling.
A separate classification or direct argument is needed to exclude every host. -/
theorem unpaid_regular_not_exceptional {X : Type*} [Finite X] [Nonempty X]
    (Q : SimpleGraph X) (D k : ℕ) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (fail : envelopeReserve Q k < minimumExposure Q D) :
    (∀d : ℕ,2≤d → ¬ Nonempty (Q ≃g zhaoGraph d)) ∧ ¬ Nonempty (Q ≃g (zhaoGraph 2)ᶜ) := by
  have rank := regular_factorCritical_exposure Q crit (Classical.choice ‹Nonempty X›) D reg
  rw [rank] at fail
  constructor
  · rintro d hd ⟨e⟩
    rw [envelopeReserve_iso e k] at fail
    have pay := (zhao_family_reserve d k hd).trans (envelope_reserve_account _ k).2
    omega
  · rintro ⟨e⟩
    rw [envelopeReserve_iso e k] at fail
    exact (Nat.not_lt_of_ge ((zhao_four_complement_reserve k).trans (envelope_reserve_account _ k).2)) fail
#print axioms zhao_family_reserve
#print axioms zhao_four_complement_reserve
#print axioms unpaid_regular_not_exceptional
end JSP452Audit.StarHost
