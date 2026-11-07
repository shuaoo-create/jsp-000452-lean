import PackingFloor

namespace JSP452Audit.StarHost
open SimpleGraph

/-- In this whole family, a minimizing host (including small-matching hosts)
    lies at most min(s,t)−1 edges below the conjectured exact formula. -/
theorem small_side_interval {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (small : (∀ i, n i ≤ 2) ∨ (∀ j, m j ≤ 2)) :
    sizeRamsey (forest n) (forest m) ≤ (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) ∧
    (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) ≤ sizeRamsey (forest n) (forest m) + (min s t-1) := by
  refine ⟨erdos561_upper n m,?_⟩
  obtain ⟨N,G,eq,force⟩ := star_min_attained n m
  have budget := small_host_budget hs ht n m hn hm pn pm small G force
  have packing := forcing_matching_floor hs ht n m pn pm G force
  omega

/-- Full equality when one target is a single star, provided one of the two
    lists (either list) has only one- or two-leaf stars. -/
theorem single_against_small_exact {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (one : s=1 ∨ t=1) (small : (∀ i, n i ≤ 2) ∨ (∀ j, m j ≤ 2)) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  obtain ⟨upper,lower⟩ := small_side_interval hs ht n m hn hm pn pm small
  omega

/-- Any insufficient forcing host must have strictly fewer than s+t−1 matching
    edges; its deficit is at most the missing number of matching edges. -/
theorem deficient_forcing_host {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (small : (∀ i, n i ≤ 2) ∨ (∀ j, m j ≤ 2)) {X : Type*} [Finite X] (G : SimpleGraph X)
    (force : Forces G (forest n) (forest m))
    (strict : G.edgeSet.ncard < ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) :
    matchingEdges G < s+t-1 ∧
      (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) - G.edgeSet.ncard ≤ (s+t-1)-matchingEdges G := by
  have h := small_host_budget hs ht n m hn hm pn pm small G force
  omega

#print axioms small_side_interval
#print axioms single_against_small_exact
#print axioms deficient_forcing_host
end JSP452Audit.StarHost
