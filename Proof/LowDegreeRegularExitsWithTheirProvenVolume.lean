import FourSelectedComponentsAlsoOutlastDegreeEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem lower_exit_after_short_eight_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (A:PricedTenMenu F) (volume:A.K.P≤2*(F.rank-matchingEdges F.G)) (red:∀i,F.n i≤7) (blue:∀j,F.m j≤7)
    (H:TenLowHistory (F.G.induce A.K.supportᶜ)) (earlier:H.high.lastCut.ncard<A.steps) :
    let b := H.high.upper.ncard
    let c := H.high.midCut.ncard
    let g := H.high.lastCut.ncard
    let l := H.sevenCut.ncard
    Nonempty (TenRegularExit A 7 (b+c+g)) ∨
      ((∀i,F.n i≤6) ∧ (∀i,F.m i≤6) ∧ Nonempty (TenRegularExit A 6 (b+c+g+l))) := by
  intro b c g l
  let O := F.G.induce A.K.supportᶜ
  have cap (x:↥(A.K.supportᶜ:Set F.X)) : Nat.card (O.neighborSet x)≤10 :=
    (induced_neighbor_count_le F.G _ x).trans (((minimal_rank_exact_source F paid).2.2.2.1 x.val).trans_eq ten)
  obtain ⟨cap7,cap6,cap5⟩ := H.remaining_caps cap
  obtain ⟨at8,at7⟩ := H.low_cut_edge_counts cap
  change O.edgeSet.ncard=(O.induce H.high.lastCutᶜ).edgeSet.ncard+8*g+b+c at at8
  change O.edgeSet.ncard=(O.induce H.sevenCutᶜ).edgeSet.ncard+7*l+b+c+g at at7
  have short := (A.bounds_when_capacity_fits paid ten volume).1
  have room (j:ℕ) (V:Set ↥(A.K.supportᶜ:Set F.X)) (pos:0<j)
      (low:∀x,Nat.card ((O.induce Vᶜ).neighborSet x)<j)
      (present:0<originalThresholdCount F.n j ∨ 0<originalThresholdCount F.m j) : A.steps≤V.ncard :=
    short.trans ((ten_closed_endpoint_sizes F paid ten A.K).2 V j pos low present)
  by_cases reaches:A.steps≤l
  · have bill : O.edgeSet.ncard=(O.induce H.high.lastCutᶜ).edgeSet.ncard+(7+1)*H.high.lastCut.ncard+(b+c) := by
      change O.edgeSet.ncard=_+(7+1)*g+(b+c);omega
    obtain ⟨V,num,_,low,fee⟩ := take_partial_stage_at_cap O H.high.lastCut 7 (b+c) cap7 bill H.seven H.stageSeven
      A.steps earlier.le reaches
    exact Or.inl ⟨⟨V,num,low,by simpa only [O,g,l,Nat.add_assoc] using fee⟩⟩
  · have absent : ¬(0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7) := fun head =>
      reaches (room 7 H.sevenCut (by decide) (fun v => Nat.lt_succ_of_le (cap6 v)) head)
    obtain ⟨_,i,j,_,_,red,blue,_⟩ := ten_central_peak_bounds_width F paid ten red blue
    have yes := (original_threshold_prefix F.n F.hn 6 i).mp red.ge
    have fill := room 6 H.sixCut (by decide) (fun v => Nat.lt_succ_of_le (cap5 v)) (Or.inl (by omega))
    have bill : O.edgeSet.ncard=(O.induce H.sevenCutᶜ).edgeSet.ncard+(6+1)*H.sevenCut.ncard+(b+c+g) := by
      change O.edgeSet.ncard=_+(6+1)*l+(b+c+g);omega
    have before : H.sevenCut.ncard≤A.steps := Nat.le_of_lt (Nat.lt_of_not_ge reaches)
    obtain ⟨V,num,_,low,fee⟩ := take_partial_stage_at_cap O H.sevenCut 6 (b+c+g) cap6 bill H.six H.stageSix
      A.steps before fill
    refine Or.inr ⟨?_,?_,⟨⟨V,num,low,by simpa only [O,g,l,Nat.add_assoc] using fee⟩⟩⟩
    · intro p;by_contra! big
      have hits := (original_threshold_prefix F.n F.hn 7 p).mp big
      exact absent (Or.inl (by omega))
    · intro p;by_contra! big
      have hits := (original_threshold_prefix F.m F.hm 7 p).mp big
      exact absent (Or.inr (by omega))


namespace TenRegularExit
variable {F:StrictFamily.{u}} {A:PricedTenMenu F} {a inc:ℕ} (E:TenRegularExit A a inc)
theorem row_price_from_volume (paid:AllSmallerPaid.{u} F.rank) (ten:diagonal F.n F.m (F.r+2)-1=10)
    (volume:A.K.P≤2*(F.rank-matchingEdges F.G)) (small:a≤10) :
    let r' := F.r+A.steps+A.K.P
    0<rowCount F.s F.t r' ∧ rowCount F.s F.t r'<F.rank ∧
      ForcingRow E.graph F.s F.t (padDemand F.n) (padDemand F.m) r' ∧
      diagonal F.n F.m (r'+2)≤a+1 ∧ E.graph.edgeSet.ncard=rowEnergy F.n F.m r'+E.surplus ∧
      E.surplus+(10-a)*A.K.P+5*A.K.eps+1+inc≤∑j∈Finset.range (11-a),widthAt F.n F.m F.r (a+j+1) := by
  intro r'
  have rank := (A.bounds_when_capacity_fits paid ten volume).2.2
  have row := A.physical_successor_row E.vertexSet E.length
  change ForcingRow E.graph F.s F.t (padDemand F.n) (padDemand F.m) r' at row
  have tall := actual_row_height_from_cap E.graph F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row rank.1 a E.cap
  have bound := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph r' row rank.2
  have eq : E.graph.edgeSet.ncard=rowEnergy F.n F.m r'+E.surplus := by change _=_+(_-rowEnergy F.n F.m r');omega
  have cap := prefix_price_through_all_higher_columns (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm a (11-a) (A.steps+A.K.P) (by omega)
  rw [←Nat.add_assoc] at cap
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m r'+a*(A.steps+A.K.P)+_ at cap
  rw [Nat.mul_add] at cap
  have headroom : (10-a)*A.K.P+a*A.K.P=10*A.K.P := by rw [←Nat.add_mul,Nat.sub_add_cancel small]
  have price := E.price
  change (F.G.induce A.K.supportᶜ).edgeSet.ncard=E.graph.edgeSet.ncard+a*A.steps+inc at price
  have split := intact_components_plus_exterior F.G A.K.support A.K.support_closed
  rw [A.K.fee] at split
  have old := F.strict
  exact ⟨rank.1,rank.2,row,tall,eq,by omega⟩

end TenRegularExit
namespace TenRegularExit
variable {F:StrictFamily.{u}} {A:PricedTenMenu F} {inc:ℕ}
theorem seven_exposure_from_volume (E:TenRegularExit A 7 inc) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (volume:A.K.P≤2*(F.rank-matchingEdges F.G)) :
    minimumExposure E.graph 7≤E.surplus+4 := by
  obtain ⟨live,smaller,row,cap,eq,_⟩ := E.row_price_from_volume paid ten volume (by decide)
  have charge := smaller_row_seven_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ F.rank
    row live smaller paid E.cap cap
  omega

theorem six_exposure_from_volume (E:TenRegularExit A 6 inc) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (volume:A.K.P≤2*(F.rank-matchingEdges F.G)) :
    minimumExposure E.graph 6≤E.surplus+4 := by
  obtain ⟨live,smaller,row,cap,eq,_⟩ := E.row_price_from_volume paid ten volume (by decide)
  by_cases few:minimumExposure E.graph 6≤3
  · omega
  · have price := six_exposure_three_piece_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ F.rank
      row live smaller.le paid E.cap cap (by omega)
    have width := (widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm E.graph _ 7 row (by decide)).trans
      ((uniformEnvelope_le_deletion E.graph 6 (by decide)).trans (deletionBudget_le_minimumExposure E.graph 6 (by decide) E.cap))
    omega


end TenRegularExit
#print axioms lower_exit_after_short_eight_stage
#print axioms TenRegularExit.row_price_from_volume
#print axioms TenRegularExit.seven_exposure_from_volume
#print axioms TenRegularExit.six_exposure_from_volume
end JSP452Audit.StarHost
