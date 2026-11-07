import PaidFourDegreeResidual
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_no_five_exterior_five_cut_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4) (U:Set F.X)
    (closed:∀x∈U,∀y,F.G.Adj x y → y∈U) (H:SixFiveFourHistory (F.G.induce Uᶜ)) :
    minimumExposure ((F.G.induce Uᶜ).induce H.fiveCutᶜ) 4≤6 := by
  let C := F.G.induce U
  let O := F.G.induce Uᶜ
  obtain ⟨A,sa⟩ := complete_degree_stage_exists C 6
  obtain ⟨J,sj⟩ := complete_degree_stage_exists (C.induce Aᶜ) 5
  let P := nestedRemoved A J
  let Q := H.fiveCut
  let S := Subtype.val '' P∪Subtype.val '' Q
  obtain ⟨whole,number⟩ := join_closed_degree_stages F.G U 6 closed A H.six sa H.stageSix
  have rigid := (strict_single_six_no_five_rigidity F paid six red blue _ whole).1
  rw [number] at rigid
  have original (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq six
  have cc (v:U) := (induced_neighbor_count_le F.G U v).trans (original v.val)
  have oc (v:↥(Uᶜ:Set F.X)) := (induced_neighbor_count_le F.G Uᶜ v).trans (original v.val)
  obtain ⟨left,lc⟩ := consecutive_six_five_account C cc A J sa sj
  obtain ⟨right,rc⟩ := consecutive_six_five_account O oc H.six H.five H.stageSix H.stageFive
  change C.edgeSet.ncard=(C.induce Pᶜ).edgeSet.ncard+5*P.ncard+A.ncard at left
  change O.edgeSet.ncard=(O.induce Qᶜ).edgeSet.ncard+5*Q.ncard+H.six.ncard at right
  have cap := caps_on_closed_residual F.G U closed P Q 4 lc rc
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
  have sizeQ := H.cut_counts.1
  change Q.ncard=_ at sizeQ
  have cost : F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+5*S.ncard+widthAt F.n F.m F.r 6 := by omega
  have total := strict_six_costed_four_residual F paid six S cap cost (by omega)
  rw [exposure_after_closed_stage_split F.G U closed P Q 4] at total
  change minimumExposure (C.induce Pᶜ) 4+minimumExposure (O.induce Qᶜ) 4≤6 at total
  change minimumExposure (O.induce Qᶜ) 4≤6
  omega

theorem envelope_after_deletion {X:Type*} [Finite X] (G:SimpleGraph X) (V:Set X) (h:ℕ) :
    uniformEnvelope G h≤V.ncard+uniformEnvelope (G.induce Vᶜ) h := by
  by_cases live:0<uniformEnvelope G h
  · obtain ⟨x,y,u,v,xp,yp,up,vp,ht,width,force⟩ := uniformEnvelope_attained G h live
    have old : ExactTypedWidth G x y (uniformEnvelope G h) := Or.inr ⟨u,v,up,vp,width,force⟩
    rcases typed_width_after_deletion G V xp yp old with zero|⟨a,b,ap,bp,size,yes⟩
    · omega
    · have bound := uniform_pair_le_envelope (G.induce Vᶜ) x y a b h xp yp ap bp ht yes
      omega
  · omega

theorem strict_no_five_fifth_envelope (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (red:∀i,F.n i≤4) (blue:∀j,F.m j≤4) (U:Set F.X)
    (closed:∀x∈U,∀y,F.G.Adj x y → y∈U) (H:SixFiveFourHistory (F.G.induce Uᶜ)) :
    uniformEnvelope (F.G.induce Uᶜ) 5≤H.fiveCut.ncard+6 := by
  let O := F.G.induce Uᶜ
  let Y := O.induce H.fiveCutᶜ
  have cap (v:↥(Uᶜ:Set F.X)) := (induced_neighbor_count_le F.G Uᶜ v).trans (((minimal_rank_exact_source F paid).2.2.2.1 v.val).trans_eq six)
  have residual := (uniformEnvelope_le_deletion Y 4 (by decide)).trans (deletionBudget_le_minimumExposure Y 4 (by decide) (H.cut_caps cap).1)
  have price := strict_no_five_exterior_five_cut_exposure F paid six red blue U closed H
  have bound := envelope_after_deletion O H.fiveCut 5
  change uniformEnvelope O 5≤H.fiveCut.ncard+uniformEnvelope Y 5 at bound
  exact bound.trans (Nat.add_le_add_left (residual.trans price) _)

#print axioms strict_no_five_exterior_five_cut_exposure
#print axioms envelope_after_deletion
#print axioms strict_no_five_fifth_envelope
end JSP452Audit.StarHost
