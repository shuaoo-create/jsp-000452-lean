import StarMinWitness
import EdgeSplit
import CopyEdgeBound

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Too few edges permit a coloring with too few edges of each color
    to contain its target. Positivity is essential for this threshold. -/
theorem cheap_host_has_avoiding_coloring {X U W : Type*} [Finite X]
    (F : SimpleGraph X) (G : SimpleGraph U) (H : SimpleGraph W)
    (red_pos : 0 < G.edgeSet.ncard) (blue_pos : 0 < H.edgeSet.ncard)
    (small : F.edgeSet.ncard < G.edgeSet.ncard + H.edgeSet.ncard - 1) :
    ∃ R ≤ F, ¬ G.IsContained R ∧ ¬ H.IsContained (F \ R) := by
  let k := min F.edgeSet.ncard (G.edgeSet.ncard-1)
  obtain ⟨R,hR,red,blue⟩ := exists_edge_split F k (min_le_left _ _)
  refine ⟨R,hR,small_edges_exclude_copy ?_,small_edges_exclude_copy ?_⟩
  · rw [red]
    dsimp [k]
    omega
  · rw [blue]
    dsimp [k]
    omega

/-- Applies to the actual sInf only once nonemptiness is established. -/
theorem edgeBudget_lower {U W : Type*} [Fintype U] [Fintype W]
    (G : SimpleGraph U) (H : SimpleGraph W)
    (red_pos : 0 < G.edgeSet.ncard) (blue_pos : 0 < H.edgeSet.ncard)
    (existsHost : (HostCounts G H).Nonempty) :
    G.edgeSet.ncard + H.edgeSet.ncard - 1 ≤ sizeRamsey G H := by
  have attained : sizeRamsey G H ∈ HostCounts G H := Nat.sInf_mem existsHost
  obtain ⟨N,F,card,forces⟩ := attained
  by_contra! h
  obtain ⟨R,hR,hr,hb⟩ := cheap_host_has_avoiding_coloring F G H red_pos blue_pos (by rwa [card])
  exact (forces R hR).elim hr hb

theorem forestEdgeLower {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ)
    (h1 : 0 < ∑ i, n i) (h2 : 0 < ∑ j, m j) :
    (∑ i, n i) + (∑ j, m j) - 1 ≤ sizeRamsey (forest n) (forest m) := by
  have hn : (forest n).edgeSet.ncard = ∑ i, n i := (Nat.card_coe_set_eq _).symm.trans (edge_count n)
  have hm : (forest m).edgeSet.ncard = ∑ i, m i := (Nat.card_coe_set_eq _).symm.trans (edge_count m)
  simpa only [hn,hm] using edgeBudget_lower (forest n) (forest m) (by rwa [hn]) (by rwa [hm])
    (star_host_counts_nonempty n m)

#print axioms cheap_host_has_avoiding_coloring
#print axioms forestEdgeLower
end JSP452Audit.StarHost
