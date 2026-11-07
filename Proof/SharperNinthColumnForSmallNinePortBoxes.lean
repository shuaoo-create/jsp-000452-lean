import NineFullNeighborsOutsideEachInternalIndependentSet
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_seven_head_ninth_shadow (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    let L := widthAt F.n F.m F.r 9
    let b := H.upper.ncard
    L-b≤R.slotDamage 3+7 ∧ L-b+9≤2*R.totalCapacity := by
  intro L b
  obtain ⟨red,blue⟩ := strict_nine_two_long_heads_at_most_seven F paid nine R long
  have third := strict_nine_ninth_column_restoration F paid nine R 3 (fun i => by have := red i;omega)
    (fun j => by have := blue j;omega)
  have capY := nine_erased_degree_cap F paid nine R
  have cap8 := (H.degree_caps capY).1
  have top := third.2 H.upper cap8
  have shadow := (strict_nine_first_exterior_eight_bound F paid nine R long H).1
  have narrow := (strict_nine_original_peak F paid nine).2.1
  change L-b≤R.slotDamage 3+max (highestWidth F.n F.m F.r-1) _ at top
  refine ⟨by omega,?_⟩
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  obtain ⟨I,tips,inc,ind,_,dom⟩ := R.internal_stage_with_both_tips cap
  let S := I∪H.upper
  have saved := R.combined_nine_neighbor_saving cap I inc ind
  have count := Set.ncard_union_eq ((R.full_stage_off_boxes H.upper H.first).symm.mono_left inc)
  change S.ncard=I.ncard+b at count
  have capS := R.original_cap_after_joining_first_stage cap I H.upper tips dom H.first
  have row := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have col := widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (F.G.induce Sᶜ) (F.r+S.ncard) 9 row (by decide)
  have exp := (uniformEnvelope_le_deletion (F.G.induce Sᶜ) 8 (by decide)).trans
    (deletionBudget_le_minimumExposure _ 8 (by decide) capS)
  change uniformEnvelope (F.G.induce Sᶜ) 9≤minimumExposure (F.G.induce Sᶜ) 8 at exp
  rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm] at col
  change L-S.ncard≤uniformEnvelope (F.G.induce Sᶜ) 9 at col
  have debt := R.first_stage_port_debt cap I H.upper inc ind H.first
  change (F.G.induce S).edgeSet.ncard+R.portCount≤2 ∧
    F.G.edgeSet.ncard+(F.G.induce S).edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard at debt
  have bs := (strict_nine_actual_stage_inventory F paid nine R H).1
  change b<portMenuGap R.capacity-(F.r+1) at bs
  have pg : portMenuGap R.capacity≤R.totalCapacity := by
    change max (min _ _) (max _ _-min _ _)≤R.capacity 0+R.capacity 1;omega
  have ic := R.independent_inside_both_boxes cap I inc ind
  have ws := strict_nine_capacity_window F paid nine R
  have sl := ws.2.1 (lt_min_iff.mp long).1
  have tl := ws.2.2.2.1 (lt_min_iff.mp long).2
  have fit : S.ncard<F.rank := by change S.ncard<F.s+F.t-1-F.r;omega
  have pair : ({(R.port 0).tip,(R.port 1).tip}:Set F.X)⊆I := by
    rintro v (a|c);exact tips ⟨0,a.symm⟩;exact tips ⟨1,(Set.mem_singleton_iff.mp c).symm⟩
  have two := Set.ncard_le_ncard pair
  have distinct : (R.port 0).tip≠(R.port 1).tip := R.disjoint_boxes.ne_of_mem (R.port 0).tip_mem (R.port 1).tip_mem
  simp only [Set.ncard_pair distinct] at two
  have topWidth : widthAt F.n F.m F.r 10=highestWidth F.n F.m F.r := by
    rw [show 10=diagonal F.n F.m (F.r+2) by omega,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm]
  have diag := shifted_head_below_spent_width F.hs F.ht F.n F.m F.hn F.hm fit
    (show widthAt F.n F.m F.r (9+1)≤S.ncard by rw [topWidth];omega)
  have positive : 0<rowCount F.s F.t (F.r+S.ncard) := by dsimp [StrictFamily.rank,rowCount] at fit ⊢;omega
  have small : rowCount F.s F.t (F.r+S.ncard)<F.rank := by dsimp [StrictFamily.rank,rowCount] at fit ⊢;omega
  have fee := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (F.G.induce Sᶜ) (F.r+S.ncard)
    8 F.rank (by decide) row positive small paid capS diag
  norm_num at fee
  have loss := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r S.ncard F.live
  rw [nine] at loss
  have strict := F.strict
  omega

#print axioms strict_nine_seven_head_ninth_shadow
end JSP452Audit.StarHost
