import CenterPeel

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Translate a funded numerical row profile into the original all-host minimum,
    using an actual minimizing finite host for the frozen definition. -/
theorem centerBudget_original {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (cost : ℕ → ℕ) (cert : ∀ r, r<s+t-1 → ∃ (i : Fin s) (j : Fin t),
      i.val+j.val=r ∧ cost r ≤ max (n i) (m j)) :
    ∑ r ∈ Finset.range (s+t-1), cost r ≤ sizeRamsey (forest n) (forest m) := by
  obtain ⟨N,G,edge,force⟩ := star_min_attained n m
  have row := (finite_targets_row_zero G hs ht n m).mpr force
  have h := repeated_center_bound n m hn hm pn pm cost cert G 0 (s+t-1) (by omega) row
  simpa only [Nat.zero_add,edge] using h

/-- The full antidiagonal formula holds whenever either entire target is a
    matching and the other is any nonempty nonincreasing star forest. -/
theorem matching_forest_exact {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (unitSide : (∀ i, n i = 1) ∨ (∀ j, m j = 1)) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  apply le_antisymm (erdos561_upper n m)
  rw [← interval_range_cost n m]
  apply centerBudget_original hs ht n m hn hm pn pm
  intro r live
  obtain ⟨i,j,hr,attains⟩ := diagonal_attained n m hs ht r live
  refine ⟨i,j,hr,?_⟩
  rw [attains]
  cases unitSide with
  | inl hu => rw [hu i]; omega
  | inr hu => rw [hu j]; omega

#print axioms centerBudget_original
#print axioms matching_forest_exact
end JSP452Audit.StarHost
