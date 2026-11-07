import EnvelopeReserve

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem sum_range_monotone (f : ℕ → ℕ) {k D : ℕ} (le : k ≤ D) :
    ∑ i ∈ Finset.range k, f i ≤ ∑ i ∈ Finset.range D, f i :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono le) (fun _ _ _ => Nat.zero_le _)

private theorem sum_range_stable (f : ℕ → ℕ) (D k : ℕ) (vanish : ∀ i, D ≤ i → f i = 0)
    (le : D ≤ k) : ∑ i ∈ Finset.range k, f i = ∑ i ∈ Finset.range D, f i := by
  symm
  apply Finset.sum_subset (Finset.range_mono le)
  intro i _ outside
  exact vanish i (Nat.le_of_not_gt (fun h => outside (Finset.mem_range.mpr h)))

theorem baseReserve_antitone (G : SimpleGraph X) : Antitone (baseReserve G) := by
  intro k D le
  exact Nat.sub_le_sub_left (Nat.add_le_add_left (sum_range_monotone _ le) _) _

theorem envelopeReserve_antitone (G : SimpleGraph X) : Antitone (envelopeReserve G) := by
  intro k D le
  exact Nat.sub_le_sub_left (Nat.add_le_add_left (sum_range_monotone _ le) _) _

theorem baseReserve_eq_at_or_above_cap (G : SimpleGraph X) (D k : ℕ)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (le : D ≤ k) :
    baseReserve G k = baseReserve G D := by
  have vanish (i : ℕ) (hi : D ≤ i) : deletionBudget G (i+1) = 0 :=
    deletionBudget_zero_above G (i+1) (by omega) (fun x => by have h := cap x; omega)
  unfold baseReserve
  rw [sum_range_stable (fun i => deletionBudget G (i+1)) D k vanish le]

theorem envelopeReserve_eq_at_or_above_cap (G : SimpleGraph X) (D k : ℕ)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (le : D ≤ k) :
    envelopeReserve G k = envelopeReserve G D := by
  have vanish (i : ℕ) (hi : D ≤ i) : uniformEnvelope G (i+2) = 0 :=
    uniform_envelope_vanishes_above G D (i+1) cap (by omega)
  unfold envelopeReserve
  rw [sum_range_stable (fun i => uniformEnvelope G (i+2)) D k vanish le]

theorem baseReserve_le_truncation (G : SimpleGraph X) (D k : ℕ)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) : baseReserve G D ≤ baseReserve G k :=
  (le_total k D).elim (fun le => baseReserve_antitone G le) (fun le => (baseReserve_eq_at_or_above_cap G D k cap le).ge)

theorem envelopeReserve_le_truncation (G : SimpleGraph X) (D k : ℕ)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) : envelopeReserve G D ≤ envelopeReserve G k :=
  (le_total k D).elim (fun le => envelopeReserve_antitone G le) (fun le => (envelopeReserve_eq_at_or_above_cap G D k cap le).ge)

#print axioms baseReserve_le_truncation
#print axioms envelopeReserve_le_truncation
#print axioms baseReserve_eq_at_or_above_cap
#print axioms envelopeReserve_eq_at_or_above_cap
end JSP452Audit.StarHost
