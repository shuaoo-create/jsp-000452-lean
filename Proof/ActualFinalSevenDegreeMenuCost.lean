import ThreeOriginalColumnsAtGeneralHeight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_final_seven_menu (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    let k := portMenuGap R.capacity-(F.r+1)
    let P := R.totalCapacity
    let h := highestWidth F.n F.m F.r
    H.midCut.ncard<k ∧ k≤H.lastCut.ncard ∧
      ∃V : Set F.X,V.ncard=k ∧
        R.erased.edgeSet.ncard=(R.erased.induce Vᶜ).edgeSet.ncard+7*k+H.upper.ncard+H.midCut.ncard ∧
        ForcingRow (R.erased.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+(k+P)) ∧
        2*P+9+R.portCount+H.upper.ncard+H.midCut.ncard≤widthAt F.n F.m F.r 8+widthAt F.n F.m F.r 9+h := by
  intro k P h
  have short := strict_nine_menu_beyond_eight F paid nine R long H
  obtain ⟨red,blue⟩ := strict_nine_two_long_heads_at_most_seven F paid nine R long
  have fits := nine_seven_head_stage_inventory F paid nine R long red blue H
  obtain ⟨V,size,cost⟩ := H.exact_last_prefix k short fits
  have gap : portMenuGap R.capacity≤F.r+k+1 := by dsimp [k];omega
  have menu := port_menu_of_gap R.capacity (F.r+k) gap
  have row := R.actual_adapted_menu_row _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row V (by rwa [size])
  have actual : ForcingRow (R.erased.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+(k+P)) := by
    simpa [size,P,Nat.add_assoc] using row
  have live := F.live
  have pos : 0<k := by change H.midCut.ncard<k at short;omega
  have smaller : rowCount F.s F.t (F.r+(k+P))<F.rank := by dsimp [StrictFamily.rank,rowCount] at live ⊢;omega
  have base := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ actual smaller
  have tax := prefix_at_three_top_columns (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm 7 (by omega) (k+P)
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have fee := (R.adapted_edge_account cap).2.2
  change F.G.edgeSet.ncard=R.erased.edgeSet.ncard+9*P+8+R.portCount at fee
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+(k+P))+7*(k+P)+widthAt F.n F.m F.r 8+widthAt F.n F.m F.r 9+h at tax
  have strict := F.strict
  exact ⟨short,fits,V,size,cost,actual,by omega⟩

#print axioms strict_nine_final_seven_menu
end JSP452Audit.StarHost
