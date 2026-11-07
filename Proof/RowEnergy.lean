import GeneralHostPotential
import EdgeBudgetLower

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Number of original antidiagonals still present at zero-based suffix row r. -/
def rowCount (s t r : ℕ) : ℕ := s + t - 1 - r

/-- Sum of their original costs, including the final one-star pair. -/
def rowEnergy {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (rowCount s t r), diagonal n m (r+k+2)

theorem rowCount_succ (s t r : ℕ) : rowCount s t (r+1) = rowCount s t r - 1 := by
  unfold rowCount
  omega

theorem rowEnergy_succ {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r : ℕ)
    (live : 0 < rowCount s t r) :
    rowEnergy n m r = diagonal n m (r+2) + rowEnergy n m (r+1) := by
  have count : rowCount s t r = rowCount s t (r+1) + 1 := by
    rw [rowCount_succ]; omega
  unfold rowEnergy
  rw [count,Finset.sum_range_succ',Nat.add_zero,add_comm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => congrArg (diagonal n m) (by omega)

theorem rowEnergy_zero {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    rowEnergy n m 0 = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  simpa [rowEnergy,rowCount] using interval_range_cost n m

/-- The unmatched correction is explicit on every actual forced suffix row. -/
theorem row_energy_budget {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (r : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    rowEnergy n m r + matchingEdges G ≤ G.edgeSet.ncard + rowCount s t r := by
  have total := potential_plus_matching G
  by_cases live : r ≤ s+t-1
  · have bound : r + rowCount s t r ≤ s+t-1 := by dsimp [rowCount]; omega
    have sub := general_row_potential hs ht n m hn hm pn pm G r _ bound row
    have countCost : (∑ k ∈ Finset.range (rowCount s t r), (diagonal n m (r+k+2)-1)) +
        rowCount s t r = rowEnergy n m r := by
      unfold rowEnergy
      calc
        _ = ∑ k ∈ Finset.range (rowCount s t r), ((diagonal n m (r+k+2)-1) + 1) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro k hk
          have idx := Finset.mem_range.mp hk
          obtain ⟨i,j,_,attains⟩ := diagonal_attained n m hs ht (r+k) (by dsimp [rowCount] at idx; omega)
          rw [attains]
          have := pn i
          have := pm j
          omega
    omega
  · have dead : rowCount s t r = 0 := by dsimp [rowCount]; omega
    simp [rowEnergy,dead]
    omega

private theorem oneStar_edge_count (a : ℕ) : (oneStar a).edgeSet.ncard = a := by
  rw [← Nat.card_coe_set_eq]
  simpa using edge_count (fun _ : Fin 1 => a)

/-- On the last row the forcing relation for its attained single-star pair
already gives the full edge cost, irrespective of the matching number. -/
theorem row_energy_last {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (r : ℕ) (last : rowCount s t r = 1)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) : rowEnergy n m r ≤ G.edgeSet.ncard := by
  have active : r < s+t-1 := by dsimp [rowCount] at last; omega
  obtain ⟨i,j,ij,attains⟩ := diagonal_attained n m hs ht r active
  have pair := row_forces_star_pair G _ _ row i j ij
  have hi : padDemand n i.val = n i := dif_pos i.isLt
  have hj : padDemand m j.val = m j := dif_pos j.isLt
  rw [hi,hj] at pair
  simp [rowEnergy,last,attains]
  by_contra! small
  obtain ⟨C,hC,red,blue⟩ := cheap_host_has_avoiding_coloring G (oneStar (n i)) (oneStar (m j))
    (by rw [oneStar_edge_count]; have := pn i; omega) (by rw [oneStar_edge_count]; have := pm j; omega)
    (by rw [oneStar_edge_count,oneStar_edge_count]; omega)
  exact (pair C hC).elim red blue

#print axioms rowEnergy_succ
#print axioms rowEnergy_zero
#print axioms row_energy_budget
#print axioms row_energy_last
end JSP452Audit.StarHost
