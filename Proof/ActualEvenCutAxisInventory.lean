import FixedPaletteFullOriginalTail
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The actual cut costs exactly 2w labels. Its remaining blue
half-order capacity is mu-w. The same nonempty blue residual is used
in both sources, even when the red tail length becomes zero. -/
theorem paired_even_cut_rows {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (w : ℕ) (room : w≤matchingEdges (G.induce K.core)) (large : matchingEdges (G.induce K.core)-w<∑j,(m j+1)/2) :
    let H := G.induce K.core
    let V := halfOrderBudget m (matchingEdges H-w)
    0<V.len ∧ ∃U:Set K.core, U.ncard=2*w ∧
      let P := incidentPalette G K U
      let Q := (restoredInternal G K) \ P
      matchingEdges P≤2*w ∧
      ForcingRow (G.induce K.rest) (s-2*w) V.len (padDemand (remainingDemand n (2*w))) (padDemand (V.entries m)) (r+K.roots.ncard) ∧
      ForcingRow (eraseInternal G K.core) (s-2*w) V.len (padDemand (remainingDemand n (2*w)))
        (padDemand (commonErasedDemand m V K.roots.ncard (matchingEdges Q))) r := by
  classical
  intro H V
  let _ := Fintype.ofFinite H.ConnectedComponent
  obtain ⟨U,count,quota⟩ := region_even_deletion_set H (ordinary_core_components_critical G K) w room
  let P := incidentPalette G K U
  have sub : P≤restoredInternal G K := fun _ _ e => e.1
  have price := (incident_palette_rank G K U).trans count.le
  have admissible := even_palette_admission G K m pm U w quota
  exact ⟨half_order_residual_nonempty m _ large,U,count,price,
    palette_original_red_tail G K P sub V n m hn hm pn pm (2*w) price admissible row⟩

theorem full_half_order_identity {t : ℕ} (m : Fin t→ℕ) (pm : ∀i,1≤m i) :
    (∑i,(m i+1)/2)=t+∑i,(m i-1)/2 := by
  have point (i:Fin t) : (m i+1)/2=1+(m i-1)/2 := by have := pm i;omega
  simp_rw [point];simp [Finset.sum_add_distrib]

/-- Uniform inventories are defined on the actual graphs, so the
new source widths may be maximized against the basic ones separately
at every height, with a common degree-deletion budget. -/
theorem exact_axis_repair_inventory {s t r D : ℕ} {X : Type*} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (ht : 0<t) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (fits : t+(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)) :
    let μ := matchingEdges (G.induce K.core)
    let w := μ+1-(t+∑j,(m j-1)/2)
    let V := halfOrderBudget m (μ-w)
    0<V.len ∧ ∀h,0<h → 2*w<originalThresholdCount n h →
      originalThresholdCount n h-2*w+V.len-1-(r+K.roots.ncard)≤uniformEnvelope (G.induce K.rest) h ∧
      originalThresholdCount n h-2*w+V.len-1-r≤uniformEnvelope (eraseInternal G K.core) h := by
  intro μ w V
  have total := full_half_order_identity m pm
  change t+(∑j,(m j-1)/2)≤μ at fits
  have room : w≤μ := by dsimp [w];omega
  have need : μ-w<∑j,(m j+1)/2 := by dsimp [w];omega
  obtain ⟨live,U,_,_,rowB,rowZ⟩ := paired_even_cut_rows G K n m hn hm pn pm row w room need
  refine ⟨live,?_⟩
  intro h pos many
  let tail := remainingDemand n (2*w)
  let rankQ := matchingEdges ((restoredInternal G K) \ incidentPalette G K U)
  let J := commonErasedDemand m V K.roots.ncard rankQ
  have size := original_threshold_le_length n h
  have S : 0<s-2*w := by omega
  have cn := threshold_tail_count n hn (2*w) h
  change originalThresholdCount tail h=originalThresholdCount n h-2*w at cn
  have liveN : 0<originalThresholdCount tail h := by omega
  have ub := widthAt_le_uniformEnvelope S live tail (V.entries m) (remainingDemand_antitone n hn _)
    (V.entries_antitone m hm) (remainingDemand_positive n pn _) (V.entries_positive m pm) _ _ h rowB pos
  have uz := widthAt_le_uniformEnvelope S live tail J (remainingDemand_antitone n hn _)
    (common_erased_antitone m hm V _ _) (remainingDemand_positive n pn _) (common_erased_positive m V _ _) _ _ h rowZ pos
  have bOne := original_threshold_one (V.entries m) (V.entries_positive m pm)
  have zOne := original_threshold_one J (common_erased_positive m V _ _)
  have Brect := actual_rectangle_le_column (r:=r+K.roots.ncard) tail (V.entries m) (remainingDemand_antitone n hn _)
    (V.entries_antitone m hm) (a:=h) (b:=1) (h:=h) (by omega) liveN (bOne.symm ▸ live)
  have Zrect := actual_rectangle_le_column (r:=r) tail J (remainingDemand_antitone n hn _)
    (common_erased_antitone m hm V _ _) (a:=h) (b:=1) (h:=h) (by omega) liveN (zOne.symm ▸ live)
  rw [cn,bOne] at Brect;rw [cn,zOne] at Zrect
  exact ⟨Brect.trans ub,Zrect.trans uz⟩

#print axioms paired_even_cut_rows
#print axioms full_half_order_identity
#print axioms exact_axis_repair_inventory
end JSP452Audit.StarHost
