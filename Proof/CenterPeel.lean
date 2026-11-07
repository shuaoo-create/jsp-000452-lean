import SelectCenter
import EdgeDeleteExact
import EdgeBudgetLower

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem select_either_center {X : Type*} [Finite X] {s t r : ℕ} (G : SimpleGraph X)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i : Fin s) (j : Fin t) (sum : i.val+j.val=r) :
    ∃ v : X, max (n i) (m j) ≤ Nat.card (G.neighborSet v) := by
  rcases le_total (n i) (m j) with left | right
  · rw [max_eq_right left]
    exact select_blue_center G n m pn row i j sum
  · rw [max_eq_left right]
    have h := row_forces_star_pair G _ _ row i j sum
    have ni : padDemand n i.val = n i := dif_pos i.isLt
    have mj : padDemand m j.val = m j := dif_pos j.isLt
    rw [ni,mj] at h
    exact high_degree_of_blue G (pm j) (forces_swap h)

/-- Every successive residual host pays any row cost certified by the larger
    member of one legal pair. No matching or independent graph bound is assumed. -/
theorem repeated_center_bound {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (cost : ℕ → ℕ) (cert : ∀ r, r<s+t-1 → ∃ (i : Fin s) (j : Fin t),
      i.val+j.val=r ∧ cost r ≤ max (n i) (m j))
    {X : Type*} [Finite X] (G : SimpleGraph X) (r len : ℕ) (live : r+len≤s+t-1)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ∑ k ∈ Finset.range len, cost (r+k) ≤ G.edgeSet.ncard := by
  induction len generalizing X r with
  | zero => simp
  | succ k ih =>
    obtain ⟨i,j,sum,afford⟩ := cert r (by omega)
    obtain ⟨v,degree⟩ := select_either_center G n m pn pm row i j sum
    have tail := row_delete_one G v _ _ (pad_antitone n hn) (pad_antitone m hm)
      (pad_positive n pn) (pad_positive m pm) row
    have tailCost := ih (G.induce {x | x ≠ v}) (r+1) (by omega) tail
    have shift : (∑ x ∈ Finset.range k, cost (r+(x+1))) =
        ∑ x ∈ Finset.range k, cost (r+1+x) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      omega
    rw [Finset.sum_range_succ',shift,Nat.add_zero,← card_neighbor_add_induce_edge_ncard G v]
    exact (Nat.add_le_add tailCost (afford.trans degree)).trans_eq (Nat.add_comm _ _)

theorem interval_range_cost {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) :
    (∑ r ∈ Finset.range (s+t-1), diagonal n m (r+2)) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  refine Finset.sum_bij (fun a _ => a+2) ?_ ?_ ?_ (by intro _ _; rfl)
  · intro a ha
    have bound := Finset.mem_range.mp ha
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro a _ b _ h
    omega
  · intro b hb
    obtain ⟨lo,hi⟩ := Finset.mem_Icc.mp hb
    exact ⟨b-2,Finset.mem_range.mpr (by omega),by omega⟩

#print axioms repeated_center_bound
end JSP452Audit.StarHost
