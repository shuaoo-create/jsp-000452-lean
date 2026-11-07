import StrictDoubleEmbeddingExcluded
import WholeCoreShiftedRows
open private JSP452Audit.StarHost.sum_colors from DegreeTwoSplit
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Isolated labels in a disjoint summand can be removed from a complete
row: every component of either positive original suffix contains an edge. -/
theorem remove_isolated_summand_row {X Y : Type*} (B:SimpleGraph X) {s t r : ℕ}
    (n m:ℕ→ℕ) (pn:∀i<s,0<n i) (pm:∀j<t,0<m j)
    (row:ForcingRow (B ⊕g (⊥:SimpleGraph Y)) s t n m r) : ForcingRow B s t n m r := by
  intro i j l q idx lenR lenB posR posB R sub
  obtain ⟨less,compl⟩ := JSP452Audit.StarHost.sum_colors sub (le_refl (⊥:SimpleGraph Y))
  rcases row i j l q idx lenR lenB posR posB _ less with red|blue
  · exact Or.inl (copy_in_left_summand R _ (forest_has_neighbor (fun x:Fin l => n (i+x.val))
      (fun x => pn _ (by have := x.isLt;omega))) red)
  · rw [compl,sdiff_self] at blue
    exact Or.inr (copy_in_left_summand (B \ R) _ (forest_has_neighbor (fun x:Fin q => m (j+x.val))
      (fun x => pm _ (by have := x.isLt;omega))) blue)

/-- Starting from the actual core-erased row and deleting the actual roots
again gives a row on the genuine exterior, retaining the other entire list
and all of its units. -/
theorem exterior_complete_red_tail {s t r D : ℕ} {X : Type*} [Finite X] (G:SimpleGraph X)
    (K:DegreeRegion G D) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    let μ := matchingEdges (G.induce K.core)
    ForcingRow (G.induce K.rest) (s-μ) t (padDemand (remainingDemand n μ)) (padDemand m) (r+K.roots.ncard) := by
  intro μ
  let Z := eraseInternal G K.core
  have erased := erase_core_complete_red_row G K n m hn row
  have shifted := row_delete_set Z K.roots (padDemand (remainingDemand n μ)) (padDemand m)
    (pad_antitone _ (remainingDemand_antitone n hn μ)) (pad_antitone m hm)
    (pad_positive _ (remainingDemand_positive n pn μ)) (pad_positive m pm) erased
  obtain ⟨cover,apart,sep⟩ := core_rest_partition G K.barrier K.pieces
  have union : K.rest∪K.core=K.rootsᶜ := by rw [Set.union_comm];exact cover
  let iso := regionSumIso Z K.rootsᶜ K.rest K.core union apart.symm (fun _ hr _ hc e => sep hc hr e.1.symm)
  have actual := forcingRow_of_iso iso.symm shifted
  have outside : Z.induce K.rest=G.induce K.rest := by
    ext a b
    exact ⟨fun e => e.1,fun e => ⟨e,fun h => Set.disjoint_left.mp apart h.1 a.property⟩⟩
  have empty : Z.induce K.core=⊥ := eraseInternal_induce_inside G K.core
  rw [outside,empty] at actual
  exact remove_isolated_summand_row (G.induce K.rest) _ _
    (pad_positive _ (remainingDemand_positive n pn μ)) (pad_positive m pm) actual

theorem exterior_complete_blue_tail {s t r D : ℕ} {X : Type*} [Finite X] (G:SimpleGraph X)
    (K:DegreeRegion G D) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (row:ForcingRow G s t (padDemand n) (padDemand m) r) :
    let μ := matchingEdges (G.induce K.core)
    ForcingRow (G.induce K.rest) s (t-μ) (padDemand n) (padDemand (remainingDemand m μ)) (r+K.roots.ncard) := by
  intro μ
  have flip := exterior_complete_red_tail G K m n hm hn pm pn (swap_positive_forcing_row G _ _ row)
  exact swap_positive_forcing_row _ _ _ flip

#print axioms remove_isolated_summand_row
#print axioms exterior_complete_red_tail
#print axioms exterior_complete_blue_tail
end JSP452Audit.StarHost
