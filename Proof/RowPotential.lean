import SmallLocalPotential
import MatchVsForest

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Summing the exact one-vertex potential losses on the nested actual hosts,
    for families with at most two leaves in each star on one side. -/
theorem small_row_potential {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (small : (∀ i, n i ≤ 2) ∨ (∀ j, m j ≤ 2))
    {X : Type*} [Finite X] (G : SimpleGraph X) (r len : ℕ) (live : r+len ≤ s+t-1)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ∑ k ∈ Finset.range len, (diagonal n m (r+k+2)-1) ≤ edgePotential G := by
  induction len generalizing X r with
  | zero => simp
  | succ k ih =>
    obtain ⟨i,j,sum,attains⟩ := diagonal_attained n m hs ht r (by omega)
    have pair := row_forces_star_pair G _ _ row i j sum
    have ni : padDemand n i.val = n i := dif_pos i.isLt
    have mj : padDemand m j.val = m j := dif_pos j.isLt
    rw [ni,mj] at pair
    have localSmall : n i ≤ 2 ∨ m j ≤ 2 := small.imp (fun h => h i) (fun h => h j)
    obtain ⟨v,paid⟩ := local_potential_small G (pn i) (pm j) localSmall pair
    have next := row_delete_one G v _ _ (pad_antitone n hn) (pad_antitone m hm)
      (pad_positive n pn) (pad_positive m pm) row
    have tail := ih (G.induce {x | x ≠ v}) (r+1) (by omega) next
    have shift : (∑ a ∈ Finset.range k, (diagonal n m (r+(a+1)+2)-1)) =
        ∑ a ∈ Finset.range k, (diagonal n m (r+1+a+2)-1) := by
      apply Finset.sum_congr rfl
      intro a _
      rw [show r+(a+1)=r+1+a by omega]
    rw [Finset.sum_range_succ',shift,Nat.add_zero,attains]
    omega

theorem sum_diagonal_sub_one {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j) :
    (∑ k ∈ Finset.range (s+t-1), (diagonal n m (k+2)-1)) + (s+t-1) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  rw [← interval_range_cost n m]
  calc
    _ = ∑ k ∈ Finset.range (s+t-1), ((diagonal n m (k+2)-1) + 1) := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k mem
      obtain ⟨i,j,_,eq⟩ := diagonal_attained n m hs ht k (Finset.mem_range.mp mem)
      rw [eq]
      have := pn i
      have := pm j
      omega

theorem small_host_budget {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (small : (∀ i, n i ≤ 2) ∨ (∀ j, m j ≤ 2))
    {X : Type*} [Finite X] (G : SimpleGraph X) (forces : Forces G (forest n) (forest m)) :
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) + matchingEdges G ≤ G.edgeSet.ncard + (s+t-1) := by
  have row := (finite_targets_row_zero G hs ht n m).mpr forces
  have h := small_row_potential hs ht n m hn hm pn pm small G 0 (s+t-1) (by omega) row
  simp only [Nat.zero_add] at h
  have each := sum_diagonal_sub_one hs ht n m pn pm
  have total := potential_plus_matching G
  omega

#print axioms small_row_potential
#print axioms small_host_budget
end JSP452Audit.StarHost
