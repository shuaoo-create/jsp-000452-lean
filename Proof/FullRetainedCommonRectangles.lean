import GapTwoRetainedLayerPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem high_boundary_retained_rectangles {s t r D b : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀i,1≤m i) (ht : 0<t) (esc : matchingEdges (G.induce K.core)<s)
    (d : ℕ) (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (positive : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2)
    (two : 0<originalThresholdCount m 2) (full : 0<originalThresholdCount m b) :
    let μ := matchingEdges (G.induce K.core)
    let a := K.roots.ncard
    let W := componentBudget (G.induce K.core) n
    let c := originalThresholdCount (W.entries n) 2
    let U := uniformEnvelope (G.induce K.rest)
    let Z := uniformEnvelope (eraseInternal G K.core)
    W.loss≤μ ∧ c+t-1-(r+a)≤U 2 ∧ W.len+originalThresholdCount m 2-1-(r+a)≤U 2 ∧
      W.len+originalThresholdCount m 2-1-r≤Z 2 ∧ c+originalThresholdCount m b-1-(r+a)≤U (b+1) := by
  intro μ a W c U Z
  obtain ⟨_,fit,brow,_,_,_,_,_⟩ := data.1
  change W.loss≤μ at fit;change μ<s at esc
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have real (j:ℕ) (hi:0<j) : widthAt (W.entries n) m (r+a) j≤U j :=
    widthAt_le_uniformEnvelope pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm _ _ j brow hi
  let J := commonErasedDemand n W a μ
  have z2 := widthAt_le_uniformEnvelope pos ht J m (common_erased_antitone n hn W a μ) hm
    (common_erased_positive n W a μ) pm _ r 2 data.2.1 (by decide)
  have pairs := exterior_binary_layer_bounds pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm (r+a) two
  have one := original_threshold_one J (common_erased_positive n W a μ)
  have zz := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm
    (a:=1) (b:=2) (h:=2) (by decide) (one.symm ▸ pos) two
  rw [one] at zz
  have rect := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=2) (b:=b) (h:=b+1) (by omega) positive full
  exact ⟨fit,((pairs.2 positive).1).trans (real 2 (by decide)),pairs.1.trans (real 2 (by decide)),zz.trans z2,
    rect.trans (real (b+1) (by omega))⟩

theorem gap_two_level_eq (D : ℕ) (deg : 6≤D) : D-2+1=D-1 ∧ 2≤D-2 := by omega

#print axioms high_boundary_retained_rectangles
#print axioms gap_two_level_eq
end JSP452Audit.StarHost