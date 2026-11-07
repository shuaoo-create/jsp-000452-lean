import HostAntidiagonal
import Mathlib.Order.Interval.Finset.Nat

namespace JSP452Audit.StarHost

private theorem diagonal_le_swapped {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (k : ℕ) :
    diagonal n m k ≤ diagonal m n k := by
  apply Finset.sup_le
  rintro ⟨i, j⟩ h
  have hk := (Finset.mem_filter.mp h).2
  have hswap : j.val + 1 + (i.val + 1) = k := by dsimp at hk; omega
  have matchPair := Finset.le_sup
      (s := (Finset.univ : Finset (Fin t × Fin s)).filter
        (fun p => p.1.val + 1 + (p.2.val + 1) = k))
      (b := (j, i)) (f := fun p => m p.1 + n p.2 - 1)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hswap⟩)
  simpa only [Nat.add_comm (n i) (m j)] using matchPair

theorem diagonal_swap {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (k : ℕ) :
    diagonal n m k = diagonal m n k :=
  le_antisymm (diagonal_le_swapped n m k) (diagonal_le_swapped m n k)

private theorem diagonal_single_right {s : ℕ} (n : Fin s → ℕ) (m : Fin 1 → ℕ) (i : Fin s) :
    diagonal n m (i.val + 2) = n i + m 0 - 1 := by
  apply le_antisymm
  · apply Finset.sup_le
    rintro ⟨a, b⟩ h
    have he := (Finset.mem_filter.mp h).2
    have hb : b = 0 := Subsingleton.elim _ _
    subst b
    have ha : a = i := by
      apply Fin.ext
      change a.val + 1 + (0 + 1) = i.val + 2 at he
      omega
    subst a
    exact le_rfl
  · simpa using antiDiag_member n m i 0

/-- With one star on the right each legal diagonal has exactly one pair. -/
theorem profile_single_right {s : ℕ} (n : Fin s → ℕ) (m : Fin 1 → ℕ) :
    (∑ k ∈ Finset.Icc 2 (s+1), diagonal n m k) = ∑ i, (n i + m 0 - 1) := by
  symm
  apply Finset.sum_bij (fun (i : Fin s) _ => i.val + 2)
  · intro i _
    apply Finset.mem_Icc.mpr
    have hi := i.isLt
    omega
  · intro a _ b _ he
    apply Fin.ext
    omega
  · intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hk
    exact ⟨⟨k-2, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
  · intro i _
    exact (diagonal_single_right n m i).symm

theorem sharp_single_single (n m : Fin 1 → ℕ) :
    (∑ k ∈ Finset.Icc 2 (1+1), diagonal n m k) = (∑ i, n i) + (∑ j, m j) - 1 := by
  rw [profile_single_right]
  simp

theorem sharp_right_unit {s : ℕ} (n : Fin s → ℕ) :
    (∑ k ∈ Finset.Icc 2 (s+1), diagonal n (fun _ : Fin 1 => 1) k) =
      (∑ i, n i) + (∑ _j : Fin 1, 1) - 1 := by
  rw [profile_single_right]
  simp

theorem sharp_left_unit {t : ℕ} (m : Fin t → ℕ) :
    (∑ k ∈ Finset.Icc 2 (1+t), diagonal (fun _ : Fin 1 => 1) m k) =
      (∑ _i : Fin 1, 1) + (∑ j, m j) - 1 := by
  simp_rw [diagonal_swap (fun _ : Fin 1 => 1) m]
  rw [Nat.add_comm 1 t, sharp_right_unit]
  simp [Nat.add_comm]

/-- Positivity of both list lengths makes every diagonal in the interval attainable. -/
theorem sharp_all_units {s t : ℕ} (hs : 0 < s) (ht : 0 < t) :
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun _ : Fin s => 1) (fun _ : Fin t => 1) k) =
      (∑ _i : Fin s, 1) + (∑ _j : Fin t, 1) - 1 := by
  have hval (k : ℕ) (hk : k ∈ Finset.Icc 2 (s+t)) :
      diagonal (fun _ : Fin s => 1) (fun _ : Fin t => 1) k = 1 := by
    obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp hk
    let i : Fin s := ⟨min (k-2) (s-1), by omega⟩
    let j : Fin t := ⟨k-2-i.val, by dsimp [i]; omega⟩
    have he : i.val + j.val + 2 = k := by dsimp [i, j]; omega
    apply le_antisymm
    · apply Finset.sup_le
      exact fun _ _ => le_rfl
    · have h := antiDiag_member (fun _ : Fin s => 1) (fun _ : Fin t => 1) i j
      rw [he] at h
      exact h
  calc
    _ = ∑ _k ∈ Finset.Icc 2 (s+t), 1 := Finset.sum_congr rfl hval
    _ = _ := by simp

#print axioms diagonal_swap
#print axioms profile_single_right
#print axioms sharp_single_single
#print axioms sharp_right_unit
#print axioms sharp_left_unit
#print axioms sharp_all_units
end JSP452Audit.StarHost
