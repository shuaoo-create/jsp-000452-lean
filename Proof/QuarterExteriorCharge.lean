import QuarterMaskCount
namespace JSP452Audit.StarHost

private theorem power_tail (k b : ℕ) :
    4*((3/4:ℚ)^k-(3/4:ℚ)^(k+b)) ≤ (b:ℚ)*(3/4:ℚ)^k := by
  induction b with
  | zero => simp
  | succ b ih =>
    have decrease := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤3/4) (by norm_num : (3/4:ℚ)≤1) (Nat.le_add_right k b)
    rw [Nat.add_succ,pow_succ,Nat.cast_succ];linarith

private theorem power_front (k : ℕ) :
    (k:ℚ)*(3/4:ℚ)^k≤4*(1-(3/4:ℚ)^k) := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    have step := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤3/4) (by norm_num : (3/4:ℚ)≤1) (Nat.le_succ k)
    have scaled := mul_le_mul_of_nonneg_left step (by positivity : (0:ℚ)≤(k:ℚ)+1)
    rw [pow_succ] at scaled ⊢
    rw [Nat.cast_succ]
    nlinarith

/-- The lost outside neighbours are charged individually to their incident
root; the geometric cost is bounded by the chord between the endpoints. -/
theorem missed_with_exterior_charge (D b : ℕ) (inside : b≤D) :
    ((D:ℚ)-1)*(3/4:ℚ)^(D+1-b) ≤ ((D:ℚ)-1)*(3/4:ℚ)^(D+1)+b := by
  let k := D+1-b
  have n : k+b=D+1 := by dsimp [k];omega
  have tail := mul_le_mul_of_nonneg_left (power_tail k b) (by positivity : (0:ℚ)≤k)
  have front := mul_le_mul_of_nonneg_left (power_front k) (by positivity : (0:ℚ)≤b)
  rw [n] at tail
  have degree : (k:ℚ)+b=(D:ℚ)+1 := by exact_mod_cast n
  have nonneg : (0:ℚ)≤(b:ℚ)*(3/4:ℚ)^(D+1) := by positivity
  have decay := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤3/4) (by norm_num : (3/4:ℚ)≤1) (show k≤D+1 by omega)
  have chord : ((k:ℚ)+b)*((3/4:ℚ)^k-(3/4:ℚ)^(D+1))≤b := by nlinarith
  rw [degree] at chord
  change ((D:ℚ)-1)*(3/4:ℚ)^k≤_
  nlinarith

theorem quarter_bound_at_eight (D : ℕ) (large : 8≤D) : (1/4:ℚ)+(3/4:ℚ)^(D+1)≤1/3 := by
  have dec := pow_le_pow_of_le_one (by norm_num : (0:ℚ)≤3/4) (by norm_num : (3/4:ℚ)≤1) (show 9≤D+1 by omega)
  norm_num at dec ⊢;linarith

#print axioms missed_with_exterior_charge
#print axioms quarter_bound_at_eight
end JSP452Audit.StarHost
