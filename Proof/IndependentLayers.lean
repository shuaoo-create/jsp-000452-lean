import SelectedEdgeSaving
import StrictReserveStep
import ComponentZeroReserve
namespace JSP452Audit.StarHost
open SimpleGraph

theorem deletion_le_after_cut_add {X : Type*} [Finite X] (G : SimpleGraph X) (I : Set X) (j : ℕ) :
    deletionBudget G j ≤ I.ncard + deletionBudget (G.induce Iᶜ) j := by
  obtain ⟨B,adm,eq⟩ := deletionBudget_attained (G.induce Iᶜ) j
  have witness := admits_remainder_of_induced_embedding (nestedCutIso G I B).symm.toEmbedding adm
  have h := deletionBudget_le_of_witness G j (outerCut I B) witness
  rwa [outerCut_ncard,eq] at h

noncomputable def savedAt {X : Type*} [Finite X] (G : SimpleGraph X) (I : Set X) (j : ℕ) : ℕ :=
  I.ncard + deletionBudget (G.induce Iᶜ) j - deletionBudget G j

theorem independent_layers_account {X : Type*} [Finite X] (G : SimpleGraph X) (I : Set X) (d : ℕ)
    (indep : G.IsIndepSet I) (degree : ∀ v∈I,Nat.card (G.neighborSet v)=d+1) :
    let H := G.induce Iᶜ
    baseReserve G (d+1)+matchingEdges G+deletionBudget G (d+1) =
      baseReserve H (d+1)+matchingEdges H+deletionBudget H (d+1)+I.ncard+
        ∑ j∈Finset.range d,savedAt G I (j+1) := by
  intro H
  have edge := selected_edge_saving G ⊥ I (d+1) bot_le indep degree (by intro x y h; exact False.elim h)
  simp only [sdiff_bot,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero,Nat.succ_mul] at edge
  change G.edgeSet.ncard = H.edgeSet.ncard + (d*I.ncard+I.ncard) at edge
  have each j : savedAt G I j + deletionBudget G j = I.ncard+deletionBudget H j :=
    Nat.sub_add_cancel (deletion_le_after_cut_add G I j)
  have totals := Finset.sum_congr (rfl : Finset.range d=Finset.range d) (fun j _ => each (j+1))
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,smul_eq_mul] at totals
  have old := base_reserve_account G (d+1)
  have new := base_reserve_account H (d+1)
  rw [Finset.sum_range_succ] at old new
  omega
#print axioms independent_layers_account
end JSP452Audit.StarHost