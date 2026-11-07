import WholeComponentCapacitiesGiveEveryOriginalPairOnTheActualSummand
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem delete_only_from_left_summand {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    (U:Set A) {s t r:ℕ} (n m:ℕ→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀i<s,0<n i) (pm:∀i<t,0<m i)
    (row:ForcingRow (Y⊕g C) s t n m r) :
    ForcingRow (Y.induce Uᶜ⊕g C) s t n m (r+U.ncard) := by
  let S := sumLabels U (∅:Set B)
  have size : S.ncard=U.ncard := by simp only [S,sum_labels_count,Set.ncard_empty,Nat.add_zero]
  have kept : Sᶜ=sumLabels Uᶜ (Set.univ:Set B) := by
    ext x;rcases x with x|x
    · rfl
    · change (¬x∈(∅:Set B)) ↔ x∈(Set.univ:Set B);simp
  have cut := row_delete_set (Y⊕g C) S n m hn hm pn pm row
  rw [size,kept] at cut
  let base := inducedSumLabelsIso Y C Uᶜ (Set.univ:Set B)
  let e := (Iso.sumCongr (Iso.refl : Y.induce Uᶜ ≃g Y.induce Uᶜ) (induceUnivIso C).symm).trans base
  exact forcingRow_of_iso e.symm cut

theorem actual_payable_exterior_menu (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    {K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)} {k c:ℕ} (P:ScaledPortPlan K k c)
    [Fintype (F.G.induce P.paidCore).ConnectedComponent] [DecidableEq (F.G.induce P.paidCore).ConnectedComponent]
    (U:Set ↥P.exterior) (menu:SplitCapacities (fun i:(F.G.induce P.paidCore).ConnectedComponent =>
      matchingEdges i.toSimpleGraph) (F.r+P.cutRoots.ncard+U.ncard)) :
    ForcingRow ((F.G.induce P.exterior).induce Uᶜ) F.s F.t (padDemand F.n) (padDemand F.m)
      (F.r+P.cutRoots.ncard+U.ncard+P.capacity) := by
  have initial := (strict_payable_exterior_constraints F paid P).2.2.2.2.2
  have step := delete_only_from_left_summand _ _ U _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) initial
  exact sum_row_whole_component_menu _ _ _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) step menu

#print axioms delete_only_from_left_summand
#print axioms actual_payable_exterior_menu
end JSP452Audit.StarHost
