import PositiveRemovalFromTheTwoActualBoxes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_long_side_actual_source_prices (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s) :
    let P := R.totalCapacity
    let a := R.roots.ncard
    let O := F.G.induce R.outside
    let Z := eraseInternal F.G R.chosen
    let W := componentBudget (F.G.induce R.chosen) F.n
    let J := commonErasedDemand F.n W a P
    let d' := F.rank-matchingEdges F.G-R.rankAllowance
    let delta := P-W.loss
    0<W.len ∧ 1≤W.loss ∧ W.loss≤P ∧
      rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta ∧
      rowCount W.len F.t F.r=a+R.outsideRank+d'+delta ∧
      0<rowCount W.len F.t (F.r+a) ∧ rowCount W.len F.t F.r<F.rank ∧
      rowEnergy (W.entries F.n) F.m (F.r+a)≤O.edgeSet.ncard ∧
      rowEnergy J F.m F.r≤Z.edgeSet.ncard ∧
      rowEnergy (W.entries F.n) F.m (F.r+a)+9*(a+P)+8≤F.G.edgeSet.ncard+R.rootDebt ∧
      rowEnergy J F.m F.r+9*P+8≤F.G.edgeSet.ncard := by
  intro P a O Z W J d' delta
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  obtain ⟨red,_,_⟩ := strict_only_double_escape F paid
  have head (i) : F.n i≤8 := by have lim := red i;rw [nine] at lim;omega
  obtain ⟨positive,fit⟩ := R.port_budget_loss_limits F.hs F.n head cap
  change 1≤W.loss at positive
  change W.loss≤P at fit
  have alive : 0<W.len := by change 0<F.s-W.loss;omega
  have number : W.len+W.loss=F.s := by change F.s-W.loss+W.loss=F.s;omega
  obtain ⟨dp,balance,_,_⟩ := strict_nine_root_deleted_row F paid nine R
  change 2≤d' at dp
  change F.s+F.t-1-(F.r+a)=P+R.outsideRank+d' at balance
  have ranks : rowCount W.len F.t (F.r+a)=R.outsideRank+d'+delta ∧
      rowCount W.len F.t F.r=a+R.outsideRank+d'+delta := by
    dsimp only [rowCount,delta];omega
  have smaller : rowCount W.len F.t F.r<F.rank := by dsimp [StrictFamily.rank,rowCount];omega
  have s2 : rowCount W.len F.t (F.r+a)<F.rank := by dsimp only [rowCount] at smaller ⊢;omega
  have rows := (strict_nine_two_physical_rows F paid nine R).1
  have payO := paid alive F.ht (W.entries F.n) F.m (W.entries_antitone F.n F.hn) F.hm
    (W.entries_positive F.n F.pn) F.pm O (F.r+a) rows.1 s2
  have payZ := paid alive F.ht J F.m (common_erased_antitone F.n F.hn W a P) F.hm
    (common_erased_positive F.n W a P) F.pm Z F.r rows.2 smaller
  have costO := (R.root_deleted_edge_account cap).1
  change F.G.edgeSet.ncard+R.rootDebt=O.edgeSet.ncard+9*(a+P)+8 at costO
  have costZ := erase_internal_edge_count F.G R.chosen
  rw [(R.region_rank_edges cap).2.1] at costZ
  change F.G.edgeSet.ncard=Z.edgeSet.ncard+(9*P+8) at costZ
  exact ⟨alive,positive,fit,ranks.1,ranks.2,by omega,smaller,payO,payZ,by omega,by omega⟩

#print axioms nine_long_side_actual_source_prices
end JSP452Audit.StarHost
