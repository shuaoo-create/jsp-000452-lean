import ThreeSuccessiveActualDegreeStages
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_actual_stage_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (H : ThreeDegreeStages R.erased 7) :
    let k := portMenuGap R.capacity-(F.r+1)
    let d := F.rank-matchingEdges F.G
    H.upper.ncard<k ∧
    (k≤H.midCut.ncard → H.upper.ncard+9+R.portCount≤k+highestWidth F.n F.m F.r) ∧
    (R.totalCapacity<min F.s F.t → 2*d+6≤H.lastCut.ncard) ∧
    (H.midCut.ncard<k → k≤H.lastCut.ncard →
      H.upper.ncard+H.midCut.ncard+9+R.portCount≤2*k+highestWidth F.n F.m F.r) := by
  intro k d
  have first := strict_nine_port_stage_gap F paid nine R H.upper H.first H.middle H.second
  have count := nested_removed_card H.upper H.middle
  change H.midCut.ncard=H.upper.ncard+H.middle.ncard at count
  have cap := H.degree_caps (nine_erased_degree_cap F paid nine R)
  have low (v) : Nat.card ((R.erased.induce H.lastCutᶜ).neighborSet v)≤6 := by
    have bound := cap.2.2 v
    omega
  refine ⟨first.1,fun fit => first.2 (by omega),?_,?_⟩
  · exact strict_nine_cost_to_drop_below_seven F paid nine R H.lastCut low
  · intro small fits
    obtain ⟨V,size,edge⟩ := H.exact_last_prefix k small fits
    have gap : portMenuGap R.capacity≤F.r+k+1 := by dsimp only [k];omega
    have menu := port_menu_of_gap R.capacity (F.r+k) gap
    have price := strict_nine_adapted_menu_price F paid nine R V (by rwa [size])
    rw [size] at price
    omega

#print axioms strict_nine_actual_stage_inventory
end JSP452Audit.StarHost
