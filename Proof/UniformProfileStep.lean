import WitnessPair
import Mathlib.Order.Interval.Finset.Nat

namespace JSP452Audit.StarHost

/-- Translating every red demand translates each legal diagonal by the same
amount. Positivity of the blue demands prevents truncated subtraction at zero.
Both maxima have explicit attaining indices, even at the two endpoints. -/
theorem diagonal_red_add {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pm : ∀ j, 1 ≤ m j) (d k : ℕ)
    (hk : k ∈ Finset.Icc 2 (s+t)) :
    diagonal (fun i => n i+d) m k = diagonal n m k + d := by
  obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hk
  let r := k-2
  have live : r < s+t-1 := by dsimp [r]; omega
  have shift : r+2 = k := by dsimp [r]; omega
  obtain ⟨i,j,ij,old⟩ := diagonal_attained n m hs ht r live
  obtain ⟨a,b,ab,new⟩ := diagonal_attained (fun i => n i+d) m hs ht r live
  have lower := antiDiag_member (fun i => n i+d) m i j
  have upper := antiDiag_member n m a b
  rw [ij,shift] at lower
  rw [ab,shift] at upper
  rw [shift] at old new
  have posj := pm j
  have posb := pm b
  omega

/-- There are exactly s+t−1 nonempty diagonals in the official expression. -/
theorem profile_red_add {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pm : ∀ j, 1 ≤ m j) (d : ℕ) :
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun i => n i+d) m k) =
      (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) + (s+t-1)*d := by
  calc
    _ = ∑ k ∈ Finset.Icc 2 (s+t), (diagonal n m k + d) :=
      Finset.sum_congr rfl (fun k hk => diagonal_red_add hs ht n m pm d k hk)
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc, smul_eq_mul]
      congr 2

theorem uniform_profile_step {s t : ℕ} (hs : 0 < s) (ht : 0 < t)
    (a : ℕ) (m : Fin t → ℕ) (pm : ∀ j, 1 ≤ m j) :
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun _ : Fin s => a+1) m k) =
      (∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun _ : Fin s => a) m k) + (s+t-1) := by
  simpa using profile_red_add hs ht (fun _ : Fin s => a) m pm 1

#print axioms diagonal_red_add
#print axioms profile_red_add
#print axioms uniform_profile_step
end JSP452Audit.StarHost
