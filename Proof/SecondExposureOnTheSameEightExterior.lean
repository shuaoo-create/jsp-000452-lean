import SevenThenSixResidualAtAnyRank
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem consecutive_eight_seven_account {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤8) (A:Set X) (B:Set ↥(Aᶜ:Set X))
    (firstStage:CompleteDegreeStage G 8 A) (secondStage:CompleteDegreeStage (G.induce Aᶜ) 7 B) :
    let S := nestedRemoved A B
    G.edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard+7*S.ncard+A.ncard ∧
      ∀v,Nat.card ((G.induce Sᶜ).neighborSet v)≤6 := by
  intro S
  have first := JSP452Audit.StarHost.degree_on_independent_full_set G A 8 firstStage.2.1 firstStage.1
  have second := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce Aᶜ) B 7 secondStage.2.1 secondStage.1
  have size := nested_removed_card A B
  have edges := nested_deletion_edges G A B
  change _=(G.induce Sᶜ).edgeSet.ncard at edges
  change S.ncard=A.ncard+B.ncard at size
  have low := complete_stage_lowers_cap G 8 A cap firstStage
  have lower := complete_stage_lowers_cap (G.induce Aᶜ) 7 B (fun v => by have := low v;omega) secondStage
  exact ⟨by omega,nested_deletion_cap G A B 6 (fun v => by have := lower v;omega)⟩

theorem strict_eight_second_exterior_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (U:Set F.X)
    (closed:∀x∈U,∀y,F.G.Adj x y → y∈U) (H:EightSevenSixHistory (F.G.induce Uᶜ)) :
    let h := highestWidth F.n F.m F.r
    minimumExposure ((F.G.induce Uᶜ).induce H.sevenCutᶜ) 6≤max 3 ((h-1+((22+2*h)/5-2)+9)/2) := by
  intro h
  let C := F.G.induce U
  let O := F.G.induce Uᶜ
  obtain ⟨A,sa⟩ := complete_degree_stage_exists C 8
  obtain ⟨J,sj⟩ := complete_degree_stage_exists (C.induce Aᶜ) 7
  let P := nestedRemoved A J
  let Q := H.sevenCut
  let S := Subtype.val '' P∪Subtype.val '' Q
  obtain ⟨whole,number⟩ := join_closed_degree_stages F.G U 8 closed A H.eight sa H.first
  have signed := (strict_eight_signed_first_residual F paid eight _ whole).2
  rw [number] at signed
  have original (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq eight
  have cc (v:U) := (induced_neighbor_count_le F.G U v).trans (original v.val)
  have oc (v:↥(Uᶜ:Set F.X)) := (induced_neighbor_count_le F.G Uᶜ v).trans (original v.val)
  obtain ⟨left,lc⟩ := consecutive_eight_seven_account C cc A J sa sj
  obtain ⟨right,rc⟩ := consecutive_eight_seven_account O oc H.eight H.seven H.first H.second
  change C.edgeSet.ncard=(C.induce Pᶜ).edgeSet.ncard+7*P.ncard+A.ncard at left
  change O.edgeSet.ncard=(O.induce Qᶜ).edgeSet.ncard+7*Q.ncard+H.eight.ncard at right
  have cap := caps_on_closed_residual F.G U closed P Q 6 lc rc
  have e := closedResidualIso F.G U closed P Q
  have edges : (C.induce Pᶜ⊕g O.induce Qᶜ).edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rw [edge_ncard_sumGraph] at edges
  have split := intact_components_plus_exterior F.G U closed
  change F.G.edgeSet.ncard=C.edgeSet.ncard+O.edgeSet.ncard at split
  have apart : Disjoint (Subtype.val '' P) (Subtype.val '' Q) := Set.disjoint_left.mpr (by
    rintro _ ⟨x,_,rfl⟩ ⟨y,_,eq⟩;exact y.property (eq ▸ x.property))
  have count : S.ncard=P.ncard+Q.ncard := by
    rw [Set.ncard_union_eq apart,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_image_of_injective _ Subtype.val_injective]
  have sizeP := nested_removed_card A J
  change P.ncard=_ at sizeP
  have sizeQ := H.counts.1
  change Q.ncard=_ at sizeQ
  have cost : F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+7*S.ncard+(A.ncard+H.eight.ncard) := by omega
  have total := strict_eight_costed_six_residual F paid eight S (A.ncard+H.eight.ncard) cap cost signed
  change minimumExposure (F.G.induce (Subtype.val '' P∪Subtype.val '' Q)ᶜ) 6≤max 3 ((h-1+((22+2*h)/5-2)+9)/2) at total
  rw [exposure_after_closed_stage_split F.G U closed P Q 6] at total
  change minimumExposure (C.induce Pᶜ) 6+minimumExposure (O.induce Qᶜ) 6≤_ at total
  change minimumExposure (O.induce Qᶜ) 6≤_
  exact (Nat.le_add_left _ _).trans total
#print axioms consecutive_eight_seven_account
#print axioms strict_eight_second_exterior_exposure
end JSP452Audit.StarHost
