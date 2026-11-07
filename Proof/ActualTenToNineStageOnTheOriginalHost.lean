import ActualComponentDeficitsAndBothTenDegreeForestEndpoints
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_complete_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (I:Set F.X) (stage:CompleteDegreeStage F.G 10 I) :
    let Y := F.G.induce Iᶜ
    let k := I.ncard
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 10
    h≤k ∧ 0<rowCount F.s F.t (F.r+k) ∧ rowCount F.s F.t (F.r+k)<F.rank ∧
    Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h ∧
    L-k≤minimumExposure Y 9 ∧ 7*minimumExposure Y 9≤38+2*h := by
  intro Y k h L
  obtain ⟨_,exactPrice,rank,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) := (degree v).trans_eq ten
  have pk := full_independent_set_le_matching F.G 10 (by decide) cap I stage.1 stage.2.1
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  have orig : widthAt F.n F.m F.r 11=h := by rw [←top];exact width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm
  obtain ⟨wide,cost,row⟩ := original_stage_width_and_cost F.G F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row
    (by decide : 0<10) cap I stage
  change widthAt F.n F.m F.r 11≤k at wide
  rw [orig] at wide
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  have live : 0<rowCount F.s F.t (F.r+k) := by change 0<F.s+F.t-1-(F.r+k);change matchingEdges F.G<F.s+F.t-1-F.r at rank;change k≤matchingEdges F.G at pk;omega
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by change F.s+F.t-1-(F.r+k)<F.s+F.t-1-F.r;change 0<F.s+F.t-1-(F.r+k) at live;omega
  have loss := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r k 10 top.le
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+10*k+widthAt F.n F.m F.r 11 at loss
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+10*k at cost
  rw [orig] at loss
  have excess : Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h := by omega
  have low (x) : Nat.card (Y.neighborSet x)≤9 := by
    have lt := complete_stage_lowers_cap F.G 10 I cap stage x
    change Nat.card (Y.neighborSet x)<10 at lt;omega
  have shifted := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r k 11
  rw [orig] at shifted
  have height := height_below_empty_column F.n F.m live (show widthAt F.n F.m (F.r+k) 11=0 by omega)
  have limit := smaller_row_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 9 F.rank
    (by decide) row live smaller paid low (by omega)
  norm_num at limit
  have col := widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 10 row (by decide)
  rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm] at col
  have needed := col.trans ((uniformEnvelope_le_deletion Y 9 (by decide)).trans (deletionBudget_le_minimumExposure Y 9 (by decide) low))
  exact ⟨wide,live,smaller,excess,needed,by omega⟩

#print axioms strict_ten_complete_stage
end JSP452Audit.StarHost
