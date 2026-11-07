import CoverDegreeSplit
import LocalPotentialFromSplit
import RowPotential
import PackingFloor
import SmallSideInterval
import UniformAccounting
import MixedRank
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Source lemma for arbitrary positive star sizes with no degree-split
    hypothesis left outstanding. -/
theorem all_local_star_potential {X : Type*} [Finite X] (G : SimpleGraph X) {a b : ℕ}
    (ha : 0<a) (hb : 0<b) (force : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, (a+b-2) + edgePotential (G.induce {x | x≠v}) ≤ edgePotential G :=
  local_potential_of_degree_split G (fun p q _ _ bound covers => degree_split_from_cover G p q bound covers)
    ha hb force

/-- Summing the exact one-vertex potential losses on the nested actual hosts,
    for arbitrary positive star sizes on both sides. -/
theorem general_row_potential {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
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
    obtain ⟨v,paid⟩ := all_local_star_potential G (pn i) (pm j) pair
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


theorem general_host_budget {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (forces : Forces G (forest n) (forest m)) :
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) + matchingEdges G ≤ G.edgeSet.ncard + (s+t-1) := by
  have row := (finite_targets_row_zero G hs ht n m).mpr forces
  have h := general_row_potential hs ht n m hn hm pn pm G 0 (s+t-1) (by omega) row
  simp only [Nat.zero_add] at h
  have each := sum_diagonal_sub_one hs ht n m pn pm
  have total := potential_plus_matching G
  omega


#print axioms all_local_star_potential
#print axioms general_host_budget
end JSP452Audit.StarHost
