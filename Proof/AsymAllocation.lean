import BarrierAllocation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace JSP452Audit.StarHost

/-- With one-sided local allowance of one, prepay half of each block into
the blue budget, then distribute all remaining units using both budgets. -/
theorem asymmetric_barrier_allocation {C : Type*} [Fintype C] (w : C → ℕ) (b p q : ℕ)
    (both : b + (∑ c, w c) ≤ p + q) (balance : b + (∑ c, w c) ≤ 2 * q + 1) :
    ∃ br bb : ℕ, ∃ red blue : C → ℕ,
      br + bb = b ∧ (∀ c, red c + blue c = w c) ∧
      br + (∑ c, red c) ≤ p ∧ bb + (∑ c, blue c) ≤ q ∧
      (∀ c, red c ≤ blue c + 1) := by
  let floor (c : C) := w c / 2
  let slack (c : C) := w c - floor c
  have local_cost (c : C) : slack c + floor c = w c := by dsimp [slack,floor]; omega
  have costs : (∑ c, slack c) + (∑ c, floor c) = ∑ c, w c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun c _ => local_cost c
  have double_floor : (∑ c, floor c) + (∑ c, floor c) ≤ ∑ c, w c := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun c _ => by dsimp [floor]; omega)
  have paid : (∑ c, floor c) ≤ q := by omega
  have afford : b + (∑ c, slack c) ≤ p + (q - ∑ c, floor c) := by omega
  obtain ⟨br,bb,r,z,bar,parts,hr,hz⟩ := barrier_allocation slack b p _ afford
  refine ⟨br,bb,r,fun c => z c + floor c,bar,?_,hr,?_,?_⟩
  · intro c
    rw [← Nat.add_assoc, parts, local_cost]
  · rw [Finset.sum_add_distrib]
    omega
  · intro c
    have := parts c
    dsimp [slack,floor] at this ⊢
    omega

#print axioms asymmetric_barrier_allocation
end JSP452Audit.StarHost
