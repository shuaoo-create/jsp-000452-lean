import ActualRemovalVolumeGuard
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem inventory_gap_implies_unpaid {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d j : ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (esc : matchingEdges (G.induce K.core)<s) (pos : 0<j)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r))
    (gap : jointLayerCapacity G K j<2*widthAt n m r j) : UnpaidHeight G K n m r j := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := component_budget_loss_le _ _
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  have b := widthAt_le_uniformEnvelope live ht (W.entries n) m (W.entries_antitone n hn) hm
    (W.entries_positive n pn) pm (G.induce K.rest) (r+a) j data.1.2.2.1 pos
  have z := widthAt_le_uniformEnvelope live ht J m (common_erased_antitone n hn W a μ) hm
    (common_erased_positive n W a μ) pm (eraseInternal G K.core) r j data.2.1 pos
  change a+2*μ+uniformEnvelope (G.induce K.rest) j+uniformEnvelope (eraseInternal G K.core) j<2*widthAt n m r j at gap
  change a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j;omega

/-- Every actual positive blue prefix occurs in both basic sources,
and their first red thresholds have length s-mu+delta. -/
theorem positive_blue_rectangle_capacity {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d j : ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (esc : matchingEdges (G.induce K.core)<s) (pos : 0<j)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) (active : 0<originalThresholdCount m j) :
    let μ := matchingEdges (G.induce K.core)
    let δ := μ-(componentBudget (G.induce K.core) n).loss
    2*(s+δ+originalThresholdCount m j)≤jointLayerCapacity G K j+2*(r+1) := by
  intro μ δ
  let a := K.roots.ncard
  let W := componentBudget (G.induce K.core) n
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := component_budget_loss_le _ _
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  have b := widthAt_le_uniformEnvelope live ht (W.entries n) m (W.entries_antitone n hn) hm
    (W.entries_positive n pn) pm (G.induce K.rest) (r+a) j data.1.2.2.1 pos
  have z := widthAt_le_uniformEnvelope live ht J m (common_erased_antitone n hn W a μ) hm
    (common_erased_positive n W a μ) pm (eraseInternal G K.core) r j data.2.1 pos
  have first := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have second := original_threshold_one J (common_erased_positive n W a μ)
  have bRect := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=1) (b:=j) (h:=j) (by omega) (first.symm ▸ live) active
  have zRect := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm
    (a:=1) (b:=j) (h:=j) (by omega) (second.symm ▸ live) active
  rw [first] at bRect
  rw [second] at zRect
  have sz : W.len+μ=s+δ := by
    change (s-W.loss)+μ=s+(μ-W.loss);change μ<s at esc;omega
  change 2*(s+δ+originalThresholdCount m j)≤
    a+2*μ+uniformEnvelope (G.induce K.rest) j+uniformEnvelope (eraseInternal G K.core) j+2*(r+1)
  omega

theorem two_head_internal_fee {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d j y : ℕ) (ht : 0<t)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀i,1≤m i)
    (esc : matchingEdges (G.induce K.core)<s) (pos : 0<j)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r)) (active : 0<originalThresholdCount m j)
    (win : WinsHeight n m r j 2 y) (present : 0<widthAt n m r j) :
    let μ := matchingEdges (G.induce K.core)
    let δ := μ-(componentBudget (G.induce K.core) n).loss
    let u := s-originalThresholdCount n 2
    2*widthAt n m r j+2*(u+δ+originalThresholdCount m j)≤jointLayerCapacity G K j+2*originalThresholdCount m y := by
  intro μ δ u
  have guard := positive_blue_rectangle_capacity G K n m r N d j ht hn hm pn pm esc pos data active
  change 2*(s+δ+originalThresholdCount m j)≤jointLayerCapacity G K j+2*(r+1) at guard
  have eq := win.2.2.2.2.2
  have count := original_threshold_le_length n 2
  dsimp only [u];omega

#print axioms inventory_gap_implies_unpaid
#print axioms positive_blue_rectangle_capacity
#print axioms two_head_internal_fee
end JSP452Audit.StarHost
