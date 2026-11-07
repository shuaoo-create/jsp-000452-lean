import NoFiveExteriorStageFloor
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
open private JSP452Audit.StarHost.degree_sum_left JSP452Audit.StarHost.degree_sum_right from ExposureComponentSum
namespace JSP452Audit.StarHost
open SimpleGraph

theorem consecutive_six_five_account {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤6) (A:Set X) (B:Set ↥(Aᶜ:Set X))
    (six:CompleteDegreeStage G 6 A) (five:CompleteDegreeStage (G.induce Aᶜ) 5 B) :
    let S := nestedRemoved A B
    G.edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard+5*S.ncard+A.ncard ∧
      ∀v,Nat.card ((G.induce Sᶜ).neighborSet v)≤4 := by
  intro S
  have first := JSP452Audit.StarHost.degree_on_independent_full_set G A 6 six.2.1 six.1
  have second := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce Aᶜ) B 5 five.2.1 five.1
  have size := nested_removed_card A B
  have edges := nested_deletion_edges G A B
  change _=(G.induce Sᶜ).edgeSet.ncard at edges
  change S.ncard=A.ncard+B.ncard at size
  have low := complete_stage_lowers_cap G 6 A cap six
  have lower := complete_stage_lowers_cap (G.induce Aᶜ) 5 B (fun v => by have := low v;omega) five
  exact ⟨by omega,nested_deletion_cap G A B 4 (fun v => by have := lower v;omega)⟩

theorem caps_on_closed_residual {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (A:Set U) (B:Set ↥(Uᶜ:Set X)) (D:ℕ)
    (left:∀v,Nat.card (((G.induce U).induce Aᶜ).neighborSet v)≤D)
    (right:∀v,Nat.card (((G.induce Uᶜ).induce Bᶜ).neighborSet v)≤D) :
    ∀v,Nat.card ((G.induce (Subtype.val '' A∪Subtype.val '' B)ᶜ).neighborSet v)≤D := by
  let C := (G.induce U).induce Aᶜ
  let O := (G.induce Uᶜ).induce Bᶜ
  let e := closedResidualIso G U closed A B
  intro v
  let x := e.symm v
  have all (z) : Nat.card ((C⊕g O).neighborSet z)≤D := by
    cases z with
    | inl a => exact (JSP452Audit.StarHost.degree_sum_left C O a).trans_le (left a)
    | inr b => exact (JSP452Audit.StarHost.degree_sum_right C O b).trans_le (right b)
  have cap := all x
  have eq := Nat.card_congr (e.mapNeighborSet x)
  change Nat.card ((C⊕g O).neighborSet x)=Nat.card ((G.induce (Subtype.val '' A∪Subtype.val '' B)ᶜ).neighborSet (e x)) at eq
  have same : e x=v := e.apply_symm_apply v
  rwa [eq,same] at cap

#print axioms consecutive_six_five_account
#print axioms caps_on_closed_residual
end JSP452Audit.StarHost
