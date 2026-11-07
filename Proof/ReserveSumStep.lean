import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace JSP452Audit.StarHost

/-- Unit losses in positive positions through k cost at most min H k over
the truncated sum of the first H positions, including the empty sum. -/
theorem sum_step_through (a b : ℕ → ℕ) (k H : ℕ)
    (low : ∀ j, 0 < j → j ≤ k → a j ≤ b j + 1)
    (high : ∀ j, k < j → a j ≤ b j) :
    (∑ i ∈ Finset.range H, a (i+1)) ≤ (∑ i ∈ Finset.range H, b (i+1)) + min H k := by
  induction H with
  | zero => simp
  | succ h ih =>
    rw [Finset.sum_range_succ,Finset.sum_range_succ]
    by_cases paid : h+1 ≤ k
    · have next := low (h+1) (by omega) paid
      omega
    · have next := high (h+1) (by omega)
      omega

/-- One matched-edge loss is affordable if position D in the old budget is
zero. Otherwise equality of matching numbers leaves all D units available. -/
theorem reserve_sum_step (a b : ℕ → ℕ) (mu mu' D H : ℕ) (posD : 0<D)
    (muDrop : mu ≤ mu' + 1)
    (low : ∀ j, 0 < j → j ≤ D → a j ≤ b j + 1)
    (high : ∀ j, D < j → a j ≤ b j)
    (atTop : a D = 0 ∨ mu = mu') :
    mu + (∑ i ∈ Finset.range H, a (i+1)) ≤ mu' + (∑ i ∈ Finset.range H, b (i+1)) + D := by
  rcases atTop with zero | same
  · have before : ∀ j, 0 < j → j ≤ D-1 → a j ≤ b j+1 :=
      fun j pos le => low j pos (by omega)
    have fromD (j : ℕ) (le : D-1 < j) : a j ≤ b j := by
      by_cases eq : j = D
      · rw [eq,zero]; exact Nat.zero_le _
      · exact high j (by omega)
    have sum := sum_step_through a b (D-1) H before fromD
    omega
  · have sum := sum_step_through a b D H low high
    omega

#print axioms sum_step_through
#print axioms reserve_sum_step
end JSP452Audit.StarHost
