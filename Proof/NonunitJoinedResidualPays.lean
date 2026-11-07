import FoldActualTopLayerPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- If a nonunit survives in J, every nonmatching winner is paid by
the ordinary paired inventories. This includes height two; its red
matching candidate requires that same nonunit threshold. -/
theorem nonunit_J_covers_lower_layers {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (esc : matchingEdges (G.induce K.core)<s) (kinds : SingleUnpaidKinds G K n m ht r)
    (data : BothActualSuccessors G K n m r N d (rowEnergy n m r))
    (nonunit : 0<originalThresholdCount (commonErasedDemand n (componentBudget (G.induce K.core) n)
      K.roots.ncard (matchingEdges (G.induce K.core))) 2)
    (j : ℕ) (lo : 2≤j) :
    2*widthAt n m r j≤jointLayerCapacity G K j+axisAllowance G K n m r j := by
  classical
  let H := G.induce K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  have fit := component_budget_loss_le H n
  change W.loss≤μ at fit
  have live : 0<W.len := by dsimp only [RemovalBudget.len];change μ<s at esc;omega
  by_cases paid : 2*widthAt n m r j≤jointLayerCapacity G K j
  · exact paid.trans (Nat.le_add_right _ _)
  have ext := data.1.2.2.1
  have zrow := data.2.1
  have b := widthAt_le_uniformEnvelope live ht (W.entries n) m (W.entries_antitone n hn) hm
    (W.entries_positive n pn) pm _ _ j ext (by omega)
  have z := widthAt_le_uniformEnvelope live ht J m (common_erased_antitone n hn W a μ) hm
    (common_erased_positive n W a μ) pm _ _ j zrow (by omega)
  have below : UnpaidHeight G K n m r j := by
    change a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt J m r j<2*widthAt n m r j
    change ¬2*widthAt n m r j≤a+2*μ+uniformEnvelope (G.induce K.rest) j+uniformEnvelope (eraseInternal G K.core) j at paid
    change widthAt (W.entries n) m (r+a) j≤uniformEnvelope (G.induce K.rest) j at b
    change widthAt J m r j≤uniformEnvelope (eraseInternal G K.core) j at z
    omega
  have present : 0<widthAt n m r j := by unfold UnpaidHeight at below;omega
  obtain ⟨x,y,xp,yp,height,nx,my,rect⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<j) present
  have wins : WinsHeight n m r j x y := ⟨xp,yp,height,nx,my,rect⟩
  have absent := (unpaid_height_missing_threshold G K n m r j hn hm pn esc below x y wins).2.1
  change originalThresholdCount J x=0 at absent
  change 0<originalThresholdCount J 2 at nonunit
  rcases kinds j x y below wins with pure|mixed
  · obtain ⟨qy,qx⟩ := pure
    subst y;subst x
    have hi : 3≤j := by
      by_contra! low;have eq : j=2 := by omega
      rw [eq] at absent;omega
    have value : axisAllowance G K n m r j=doubleEnvelopeLoss G K n m r j := by
      unfold axisAllowance;exact if_pos ⟨hi,wins⟩
    rw [value]
    change 2*widthAt n m r j≤jointLayerCapacity G K j+(2*widthAt n m r j-jointLayerCapacity G K j)
    omega
  · rw [mixed.1] at absent;omega

#print axioms nonunit_J_covers_lower_layers
end JSP452Audit.StarHost
