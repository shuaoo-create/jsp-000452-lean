import JoinTheTwoRealEightDegreeStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_two_long_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) : False := by
  obtain ⟨H⟩ := three_degree_stages_exist R.erased 7
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  obtain ⟨I,tips,inside,ind,_,dom⟩ := R.internal_stage_with_both_tips cap
  let S := I∪H.upper
  have size := Set.ncard_union_eq ((R.full_stage_off_boxes H.upper H.first).symm.mono_left inside)
  change S.ncard=I.ncard+H.upper.ncard at size
  have many := (strict_nine_two_long_capacity_is_large F paid nine R long H).1
  have pos : 0<S.ncard := by omega
  have limits := R.independent_inside_both_boxes cap I inside ind
  have stage := (strict_nine_actual_stage_inventory F paid nine R H).1
  have menu : portMenuGap R.capacity≤R.totalCapacity := by
    change max (min _ _) (max _ _-min _ _)≤R.capacity 0+R.capacity 1;omega
  have win := strict_nine_capacity_window F paid nine R
  have sl := win.2.1 (lt_min_iff.mp long).1
  have tl := win.2.2.2.1 (lt_min_iff.mp long).2
  have fit : S.ncard<F.rank := by change S.ncard<F.s+F.t-1-F.r;omega
  have price := R.first_stage_port_debt cap I H.upper inside ind H.first
  change (F.G.induce S).edgeSet.ncard+R.portCount≤2 ∧
    F.G.edgeSet.ncard+(F.G.induce S).edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard at price
  have cap1 := R.original_cap_after_joining_first_stage cap I H.upper tips dom H.first
  obtain ⟨I',sub,inside',count,cap2,fee2⟩ := R.actual_second_stage H (nine_erased_degree_cap F paid nine R) I inside tips cap1
  let T := I'∪H.midCut
  have fee1 : (F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard≤F.G.edgeSet.ncard+2 := by omega
  have upper := nine_two_stage_seven_exposure_ceiling F paid nine S T pos fit count cap1 cap2 fee1 fee2
  have transfer := R.actual_stage_exposure_transfer I' H.midCut inside' (tips.trans sub) 7 (by decide)
  change minimumExposure (R.erased.induce H.midCutᶜ) 7≤minimumExposure (F.G.induce Tᶜ) 7 at transfer
  have lower := strict_nine_final_exterior_exposure_at_least_ten F paid nine R long H
  omega

theorem strict_nine_exactly_one_short_list (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) :
    let P := R.totalCapacity
    (F.s+5≤P ∧ P+F.r+10≤F.t) ∨ (F.t+5≤P ∧ P+F.r+10≤F.s) := by
  intro P
  obtain ⟨red,blue⟩ := (strict_nine_capacity_window F paid nine R).2.2.2.2
  have noShort := strict_nine_double_short_impossible F paid nine R
  have noLong := strict_nine_two_long_impossible F paid nine R
  rcases red with rs|rl <;> rcases blue with bs|bl
  · exact (noShort (by omega) (by omega)).elim
  · exact Or.inl ⟨rs,bl⟩
  · exact Or.inr ⟨bs,rl⟩
  · exact (noLong (lt_min (by omega) (by omega))).elim

#print axioms strict_nine_two_long_impossible
#print axioms strict_nine_exactly_one_short_list
end JSP452Audit.StarHost
