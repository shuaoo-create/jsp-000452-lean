import WholeComponentPieces
import ComponentSurplusSum

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)

private theorem surplus_selected (T : Finset (G.induce Sᶜ).ConnectedComponent) (D : ℕ) :
    edgeSurplus (T.sup (wholePiece G S)) D =
      ∑ c ∈ T, edgeSurplus ((G.induce Sᶜ).induce c.supp) D := by
  classical
  let w (c : (G.induce Sᶜ).ConnectedComponent) := edgeSurplus ((G.induce Sᶜ).induce c.supp) D
  have total := core_surplus_eq_sum G S (T : Set _) D
  have sizes : (∑ c ∈ T, w c) = ∑ c : ↥(T : Set _), w c.val := Finset.sum_subtype T (fun _ => Iff.rfl) w
  change _ = ∑ c ∈ T, w c
  rw [sizes,← total]
  simp only [edgeSurplus,matchingEdges_sup_wholePiece,edgeCount_sup_wholePiece]

/-- Evaluate the signed identity at heights zero and one. The original edge
counts cancel, giving the exact matching number for any selected components. -/
theorem matchingEdges_selected_components (T : Finset (G.induce Sᶜ).ConnectedComponent) :
    matchingEdges (T.sup (wholePiece G S)) =
      ∑ c ∈ T, matchingEdges ((G.induce Sᶜ).induce c.supp) := by
  have atZero := surplus_selected G S T 0
  have atOne := surplus_selected G S T 1
  simp only [edgeSurplus,Nat.cast_zero,zero_mul,sub_zero] at atZero
  simp only [edgeSurplus,Nat.cast_one,one_mul,Finset.sum_sub_distrib,atZero] at atOne
  have rank : (matchingEdges (T.sup (wholePiece G S)) : ℤ) =
      ∑ c ∈ T, (matchingEdges ((G.induce Sᶜ).induce c.supp) : ℤ) := by omega
  exact_mod_cast rank

theorem selected_component_edge_account (T : Finset (G.induce Sᶜ).ConnectedComponent) (D : ℕ) :
    ((T.sup (wholePiece G S)).edgeSet.ncard : ℤ) =
      (D : ℤ) * (∑ c ∈ T, matchingEdges ((G.induce Sᶜ).induce c.supp) : ℕ) +
      ∑ c ∈ T, edgeSurplus ((G.induce Sᶜ).induce c.supp) D := by
  have total := surplus_selected G S T D
  unfold edgeSurplus at total
  rw [matchingEdges_selected_components] at total
  change _ = _ + ∑ c ∈ T,
    (((G.induce Sᶜ).induce c.supp).edgeSet.ncard - (D : ℤ) * matchingEdges ((G.induce Sᶜ).induce c.supp))
  omega

/-- Any injection of selected indices into components can be used directly.
In particular take e=Subtype.val on a set of eligible components. -/
theorem component_totals_on_labels {I : Type*}
    (e : I ↪ (G.induce Sᶜ).ConnectedComponent) (T : Finset I) (D : ℕ) :
    matchingEdges (T.sup (fun i => wholePiece G S (e i))) =
      (∑ i ∈ T, matchingEdges ((G.induce Sᶜ).induce (e i).supp)) ∧
    ((T.sup (fun i => wholePiece G S (e i))).edgeSet.ncard : ℤ) =
      (D : ℤ) * (∑ i ∈ T, matchingEdges ((G.induce Sᶜ).induce (e i).supp) : ℕ) +
      ∑ i ∈ T, edgeSurplus ((G.induce Sᶜ).induce (e i).supp) D := by
  have rk := matchingEdges_selected_components G S (T.map e)
  have ec := selected_component_edge_account G S (T.map e) D
  simp only [Finset.sup_map,Finset.sum_map,Function.comp_def] at rk ec
  exact ⟨rk,ec⟩

#print axioms matchingEdges_selected_components
#print axioms selected_component_edge_account
#print axioms component_totals_on_labels
end JSP452Audit.StarHost
