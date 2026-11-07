import NoUnitsKernel

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The old-color restoration step can spend the exact rank in distinct edges
    of one maximum matching whenever both input forests have no unit star. -/
theorem large_matching_for_erase {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (strongN : ∀ i, 2≤n i) (strongM : ∀ j, 2≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (h : Forces G (forest n) (forest m)) :
    ∃ M : G.Subgraph, M.IsMatching ∧ s+t-1 ≤ M.edgeSet.ncard := by
  obtain ⟨M,hM,sz⟩ := exists_maximum_matching G
  refine ⟨M,hM,?_⟩
  rw [sz]
  exact unit_free_matching_floor G hs ht n m strongN strongM h

/-- Transfer a lower estimate valid on all actual forcing graphs on finite
    initial segments to the frozen minimum, where an actual minimizer exists. -/
theorem exact_of_forcing_lower {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (lower : ∀ (N : ℕ) (G : SimpleGraph (Fin N)), Forces G (forest n) (forest m) →
       (∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) ≤ G.edgeSet.ncard) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  apply le_antisymm (erdos561_upper n m)
  obtain ⟨N,G,eq,h⟩ := star_min_attained n m
  exact (lower N G h).trans_eq eq

#print axioms large_matching_for_erase
#print axioms exact_of_forcing_lower
end JSP452Audit.StarHost
