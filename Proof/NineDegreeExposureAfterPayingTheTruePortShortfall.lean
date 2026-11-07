import TrueCostAndCapacityOfTheOriginalTenToNineReduction
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_costed_first_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (S:Set F.X) (delta:ℕ)
    (low:∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤9)
    (cost:F.G.edgeSet.ncard+delta=(F.G.induce Sᶜ).edgeSet.ncard+10*S.ncard) (fit:S.ncard<F.rank) :
    let Y := F.G.induce Sᶜ
    let h := highestWidth F.n F.m F.r
    h≤S.ncard ∧ widthAt F.n F.m F.r 10-S.ncard≤minimumExposure Y 9 ∧
      7*minimumExposure Y 9≤38+2*h+2*delta := by
  intro Y h
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  have orig : widthAt F.n F.m F.r 11=h := by rw [←top];exact width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm
  have feasible : admits_matching_remainder Y 10 := by
    refine ⟨⊥,fun _ a => a.elim,?_⟩
    intro x;rw [Subgraph.spanningCoe_bot,sdiff_bot];exact low x
  have oldWidth := original_width_le_deletion F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r 10 F.row (by decide)
  have wide : h≤S.ncard := orig ▸ oldWidth.trans (deletionBudget_le_of_witness F.G 10 S feasible)
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  have live : 0<rowCount F.s F.t (F.r+S.ncard) := by
    change S.ncard<F.s+F.t-1-F.r at fit;dsimp only [rowCount];omega
  have smaller : rowCount F.s F.t (F.r+S.ncard)<F.rank := by
    dsimp only [rowCount,StrictFamily.rank] at live ⊢;omega
  have row := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  have loss := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r S.ncard 10 top.le
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+S.ncard)+10*S.ncard+widthAt F.n F.m F.r 11 at loss
  rw [orig] at loss
  have shifted := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r S.ncard 11
  rw [orig] at shifted
  have height := height_below_empty_column F.n F.m live (show widthAt F.n F.m (F.r+S.ncard) 11=0 by omega)
  have limit := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+S.ncard) 9 F.rank
    (by decide) row live smaller paid low (by omega)
  norm_num at limit
  have col := widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+S.ncard) 10 row (by decide)
  rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm] at col
  have needed := col.trans ((uniformEnvelope_le_deletion Y 9 (by decide)).trans (deletionBudget_le_minimumExposure Y 9 (by decide) low))
  change F.G.edgeSet.ncard+delta=Y.edgeSet.ncard+10*S.ncard at cost
  have strict := F.strict
  exact ⟨wide,needed,by omega⟩

theorem ten_port_first_stage_exposure (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (I:Set W.available) (inner:CompleteDegreeStage (F.G.induce W.available) 10 I)
    (B:Set ↥(W.supportᶜ:Set F.X)) (outer:CompleteDegreeStage W.outside 10 B) :
    let S := W.spent I B
    let h := highestWidth F.n F.m F.r
    let bound := (38+2*h+2*W.seedLoss)/7
    S.ncard<F.rank ∧ minimumExposure (F.G.induce Sᶜ) 9≤bound ∧ minimumExposure (W.outside.induce Bᶜ) 9≤bound ∧
      widthAt F.n F.m F.r 10+W.targetPorts≤W.rank+B.ncard+bound := by
  intro S h bound
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  obtain ⟨small,size,fee,low⟩ := W.first_reduction cap I inner B outer
  change S.ncard+W.targetPorts≤W.rank+B.ncard at size
  have out := ten_port_steps_outlast_ten F paid ten W length B outer
  have kd := (TenPortSupport.whole_piece_rank_progress F W length (by have := (minimal_strict_source_deficit F paid).2.2;omega)).2.2.1
  have fit : S.ncard<F.rank := by omega
  obtain ⟨_,bill,lim⟩ := ten_costed_first_exposure F paid ten S W.seedLoss low fee fit
  have transfer := W.paid_cut_exposure I B 9
  change minimumExposure (W.outside.induce Bᶜ) 9≤minimumExposure (F.G.induce Sᶜ) 9 at transfer
  change 7*minimumExposure (F.G.induce Sᶜ) 9≤38+2*h+2*W.seedLoss at lim
  dsimp only [bound];omega

#print axioms ten_costed_first_exposure
#print axioms ten_port_first_stage_exposure
end JSP452Audit.StarHost
