import UniformVsForest
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The exact shift only needs funding by a real matching in each minimizing
    candidate host; no non-unit assumption is hidden in the restoration itself. -/
theorem exact_shift_with_funding {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (mPos : ∀ j, 1≤m j)
    (less : sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k)
    (funding : ∀ (N : ℕ) (G : SimpleGraph (Fin N)),
      Forces G (forest (fun i => n i+1)) (forest m) → s+t-1 ≤ matchingEdges G) :
    sizeRamsey (forest (fun i => n i+1)) (forest m) =
      ∑ k ∈ Finset.Icc 2 (s+t), diagonal (fun i => n i+1) m k := by
  apply exact_of_forcing_lower
  intro N G h
  obtain ⟨M,hM,sz⟩ := exists_maximum_matching G
  have paid := funding N G h
  have h' := forcing_erase_matching G M hM n m h
  have hcost := sizeRamsey_le_of_host _ _ _ h'
  rw [less] at hcost
  have cost := profile_red_add hs ht n m mPos 1
  have edges := eraseMatching_edge_count M
  rw [cost]
  omega

#print axioms exact_shift_with_funding
end JSP452Audit.StarHost
