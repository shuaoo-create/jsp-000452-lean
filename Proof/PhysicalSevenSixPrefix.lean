import SevenIncidencesAfterTwoDegreeLoss
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph

theorem seven_six_prefix_exists {X:Type*} [Finite X] (H:SimpleGraph X) (z t:ℕ) (E B:Set X)
    (cap:∀x,Nat.card (H.neighborSet x)≤7) (many:6*z+3≤E.ncard)
    (full:∀x∈E,Nat.card (H.neighborSet x)=7) (stage:CompleteDegreeStage H 7 B)
    (short:B.ncard<t) (fit:t≤z) :
    ∃A:Set X,B⊆A ∧ A.ncard=t ∧
      H.edgeSet.ncard=(H.induce Aᶜ).edgeSet.ncard+6*t+B.ncard ∧
      ∀x,Nat.card ((H.induce Aᶜ).neighborSet x)≤6 := by
  let J := H.induce Bᶜ
  obtain ⟨C,stageC⟩ := complete_degree_stage_exists J 6
  have capJ (x) : Nat.card (J.neighborSet x)≤6 := by
    have lt := complete_stage_lowers_cap H 7 B cap stage x
    change Nat.card ((H.induce Bᶜ).neighborSet x)≤6;omega
  have capLow (x) : Nat.card ((J.induce Cᶜ).neighborSet x)≤5 := by
    have lt := complete_stage_lowers_cap J 6 C capJ stageC x;omega
  let S := nestedRemoved B C
  have capS := nested_deletion_cap H B C 5 capLow
  have cost := seven_to_five_incidence_cost H cap E S full capS
  have size := nested_removed_card B C
  change S.ncard=B.ncard+C.ncard at size
  have needed : t-B.ncard≤C.ncard := by omega
  obtain ⟨V,_,num,edge⟩ := subset_of_stage_price J 6 C stageC (t-B.ncard) needed
  let A := nestedRemoved B V
  have count := nested_removed_card B V
  have first := JSP452Audit.StarHost.degree_on_independent_full_set H B 7 stage.2.1 stage.1
  have last := nested_deletion_edges H B V
  change (J.induce Vᶜ).edgeSet.ncard=(H.induce Aᶜ).edgeSet.ncard at last
  change A.ncard=B.ncard+V.ncard at count
  refine ⟨A,Set.subset_union_left,by omega,?_,?_⟩
  · change H.edgeSet.ncard=J.edgeSet.ncard+7*B.ncard at first
    omega
  · exact nested_deletion_cap H B V 6 (fun x => (induced_neighbor_count_le J Vᶜ x).trans (capJ x.val))

#print axioms seven_six_prefix_exists
end JSP452Audit.StarHost
