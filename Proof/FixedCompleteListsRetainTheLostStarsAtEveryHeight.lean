import IntersectTwoFixedForcingRowsBeforeChoosingTheExteriorColouring
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable abbrev fixedCoreList {A:Type*} [Finite A] {s:ℕ} (C:SimpleGraph A) (n:Fin s→ℕ) (l:ℕ) :=
  protectedDemand n ((componentBudget C n).entries n) l

theorem fixed_core_threshold_loss {A:Type*} [Finite A] (C:SimpleGraph A) {s:ℕ} (n:Fin s→ℕ) (hn:Antitone n)
    (l h:ℕ) : originalThresholdCount n h≤originalThresholdCount (fixedCoreList C n l) h+
      (min (matchingEdges C) (Nat.card A/(h+1))-l) := by
  let W := componentBudget C n
  let f := originalThresholdCount n h
  let g := originalThresholdCount (W.entries n) h
  have cap := actual_threshold_capacity C n hn h
  have slot := component_slot_vertex_price C h
  rw [Nat.mul_comm] at slot
  have order := (Nat.le_div_iff_mul_le (by omega : 0<h+1)).mpr slot
  obtain ⟨T,lost⟩ := threshold_removal_witness n hn W h
  have inside := Finset.card_le_card (Finset.filter_subset (fun z => h≤n z) T.val)
  have rank := ((mem_component_budget C n T.val).mp T.property).1
  change f≤g+_ at cap lost
  change f≤originalThresholdCount (protectedDemand n (W.entries n) l) h+_
  rw [protected_demand_threshold n _ hn (W.entries_antitone n hn)]
  change f≤min f (g+l)+_
  omega

theorem fixed_core_list_row {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B) {s t r:ℕ}
    (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (row:ForcingRow (Y⊕g C) s t (padDemand n) (padDemand m) r) (U:Set A) (l:ℕ) (legal:l≤r+U.ncard+1) :
    let W := componentBudget C n
    let V := componentBudget C m
    ForcingRow (Y.induce Uᶜ) (min s (W.len+l)) (min t (V.len+l))
      (padDemand (fixedCoreList C n l)) (padDemand (fixedCoreList C m l)) (r+U.ncard+l) := by
  intro W V
  have start := delete_only_from_left_summand Y C U _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  have red := one_budget_on_sum_row _ C n m pm W (component_budget_admits C n pn) start
  have blue := one_budget_on_sum_row _ C m n pn V (component_budget_admits C m pm) (swap_positive_forcing_row _ _ _ start)
  exact intersect_two_fixed_rows _ n m _ _ l legal red (swap_positive_forcing_row _ _ _ blue)

#print axioms fixed_core_threshold_loss
#print axioms fixed_core_list_row
end JSP452Audit.StarHost
