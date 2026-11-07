import ExposureEightAtPositiveAndExhaustedRanks
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem consecutive_ten_nine_account {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤10) (A:Set X) (B:Set ↥(Aᶜ:Set X))
    (firstStage:CompleteDegreeStage G 10 A) (secondStage:CompleteDegreeStage (G.induce Aᶜ) 9 B) :
    let S := nestedRemoved A B
    G.edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard+9*S.ncard+A.ncard ∧
      ∀v,Nat.card ((G.induce Sᶜ).neighborSet v)≤8 := by
  intro S
  have first := JSP452Audit.StarHost.degree_on_independent_full_set G A 10 firstStage.2.1 firstStage.1
  have second := JSP452Audit.StarHost.degree_on_independent_full_set (G.induce Aᶜ) B 9 secondStage.2.1 secondStage.1
  have size := nested_removed_card A B
  have edges := nested_deletion_edges G A B
  change _=(G.induce Sᶜ).edgeSet.ncard at edges
  change S.ncard=A.ncard+B.ncard at size
  have low := complete_stage_lowers_cap G 10 A cap firstStage
  have lower := complete_stage_lowers_cap (G.induce Aᶜ) 9 B (fun v => by have := low v;omega) secondStage
  exact ⟨by omega,nested_deletion_cap G A B 8 (fun v => by have := lower v;omega)⟩

theorem strict_ten_second_exterior_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (U:Set F.X)
    (closed:∀x∈U,∀y,F.G.Adj x y → y∈U) (red:∀i,F.n i≤8) (blue:∀j,F.m j≤8) (H:ThreeDegreeStages (F.G.induce Uᶜ) 8) :
    let h := highestWidth F.n F.m F.r
    minimumExposure ((F.G.induce Uᶜ).induce H.midCutᶜ) 8≤max 4 ((h-1+((38+2*h)/7-2)+16)/3) := by
  intro h
  let C := F.G.induce U
  let O := F.G.induce Uᶜ
  obtain ⟨A,sa⟩ := complete_degree_stage_exists C 10
  obtain ⟨J,sj⟩ := complete_degree_stage_exists (C.induce Aᶜ) 9
  let P := nestedRemoved A J
  let Q := H.midCut
  let S := Subtype.val '' P∪Subtype.val '' Q
  obtain ⟨whole,number⟩ := join_closed_degree_stages F.G U 10 closed A H.upper sa H.first
  have signed := (ten_signed_first_stage F paid ten red blue _ whole)
  rw [number] at signed
  have original (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have cc (v:U) := (induced_neighbor_count_le F.G U v).trans (original v.val)
  have oc (v:↥(Uᶜ:Set F.X)) := (induced_neighbor_count_le F.G Uᶜ v).trans (original v.val)
  obtain ⟨left,lc⟩ := consecutive_ten_nine_account C cc A J sa sj
  obtain ⟨right,rc⟩ := consecutive_ten_nine_account O oc H.upper H.middle H.first H.second
  change C.edgeSet.ncard=(C.induce Pᶜ).edgeSet.ncard+9*P.ncard+A.ncard at left
  change O.edgeSet.ncard=(O.induce Qᶜ).edgeSet.ncard+9*Q.ncard+H.upper.ncard at right
  have cap := caps_on_closed_residual F.G U closed P Q 8 lc rc
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
  have sizeQ := nested_removed_card H.upper H.middle
  change Q.ncard=_ at sizeQ
  have cost : F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard+(A.ncard+H.upper.ncard) := by omega
  have total := strict_ten_costed_eight_residual F paid ten S (A.ncard+H.upper.ncard) cap cost signed
  change minimumExposure (F.G.induce (Subtype.val '' P∪Subtype.val '' Q)ᶜ) 8≤max 4 ((h-1+((38+2*h)/7-2)+16)/3) at total
  rw [exposure_after_closed_stage_split F.G U closed P Q 8] at total
  change minimumExposure (C.induce Pᶜ) 8+minimumExposure (O.induce Qᶜ) 8≤_ at total
  change minimumExposure (O.induce Qᶜ) 8≤_
  exact (Nat.le_add_left _ _).trans total
#print axioms consecutive_ten_nine_account
#print axioms strict_ten_second_exterior_exposure
end JSP452Audit.StarHost
