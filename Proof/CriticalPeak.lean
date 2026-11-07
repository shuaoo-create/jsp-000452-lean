import GeneralHostPotential
import FiniteDemand

namespace JSP452Audit.StarHost
open SimpleGraph
variable {s t r : ℕ} {X : Type*} [Finite X]

/-- For a maximizing legal pair, local potential loss forces a real vertex
    with degree at least the current antidiagonal value minus one. -/
theorem vertex_at_row_peak (G : SimpleGraph X) (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (live : r<s+t-1) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ∃ v : X, diagonal n m (r+2)-1 ≤ Nat.card (G.neighborSet v) := by
  obtain ⟨i,j,sum,att⟩ := diagonal_attained n m hs ht r live
  have pair := row_forces_star_pair G _ _ row i j sum
  have ni : padDemand n i.val = n i := dif_pos i.isLt
  have mj : padDemand m j.val = m j := dif_pos j.isLt
  rw [ni,mj] at pair
  obtain ⟨v,paid⟩ := all_local_star_potential G (pn i) (pm j) pair
  have edge := card_neighbor_add_induce_edge_ncard G v
  have dec := matchingEdges_delete_le G v
  have all := potential_plus_matching G
  have rem := potential_plus_matching (G.induce {x | x≠v})
  exact ⟨v,by omega⟩

/-- If a maximizing pair contains a single edge, one monochrome coloring
    forces a vertex paying the *full* antidiagonal cost. -/
theorem vertex_at_unit_peak (G : SimpleGraph X) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i : Fin s) (j : Fin t) (sum : i.val+j.val=r)
    (att : diagonal n m (r+2) = n i + m j - 1) (unit : n i=1 ∨ m j=1) :
    ∃ v : X, diagonal n m (r+2) ≤ Nat.card (G.neighborSet v) := by
  have pair := row_forces_star_pair G _ _ row i j sum
  have ni : padDemand n i.val = n i := dif_pos i.isLt
  have mj : padDemand m j.val = m j := dif_pos j.isLt
  rw [ni,mj] at pair
  rcases unit with hi | hj
  · obtain ⟨v,h⟩ := high_degree_of_blue G (pn i) pair
    exact ⟨v,by omega⟩
  · obtain ⟨v,h⟩ := high_degree_of_blue G (pm j) (forces_swap pair)
    exact ⟨v,by omega⟩

#print axioms vertex_at_row_peak
#print axioms vertex_at_unit_peak
end JSP452Audit.StarHost
