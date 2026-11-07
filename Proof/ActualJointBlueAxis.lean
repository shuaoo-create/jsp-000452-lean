import JointUnitTwoEndpointBalance
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Both successors on the one original graph contain the same pure
opposing prefix. The loss at the roots occurs only on the exterior row. -/
theorem joint_common_blue_axis {s t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i)
    (esc : matchingEdges (G.induce K.core)<s) (r j : ℕ) (blue : 0<originalThresholdCount m j) :
    let Q := basicCapacity G K n m r j
    let g := originalThresholdCount m j
    2*(s+g-1-r)≤Q ∧ 2*s+2*g≤Q+2+2*r := by
  intro Q g
  let H := G.induce K.core
  let μ := matchingEdges H
  let a := K.roots.ncard
  let W := componentBudget H n
  let J := commonErasedDemand n W a μ
  have fit : W.loss≤μ := component_budget_loss_le _ _
  change μ<s at esc
  have len : s≤W.len+μ := by dsimp only [RemovalBudget.len];omega
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have first := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have second := original_threshold_one J (common_erased_positive n W a μ)
  have left := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=1) (b:=j) (h:=j) (by omega) (first.symm ▸ pos) blue
  have right := actual_rectangle_le_column (r:=r) J m (common_erased_antitone n hn W a μ) hm
    (a:=1) (b:=j) (h:=j) (by omega) (second.symm ▸ pos) blue
  rw [first] at left;rw [second] at right
  exact joint_blue_axis_budget s W.len μ a r g _ _ len left right

#print axioms joint_common_blue_axis
end JSP452Audit.StarHost