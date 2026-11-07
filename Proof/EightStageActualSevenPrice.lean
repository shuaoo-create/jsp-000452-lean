import FullIndependentSetFitsOriginalMatching
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_eight_complete_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (I:Set F.X) (stage:CompleteDegreeStage F.G 8 I) :
    let Y := F.G.induce Iᶜ
    let k := I.ncard
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 8
    h≤k ∧ 0<rowCount F.s F.t (F.r+k) ∧ rowCount F.s F.t (F.r+k)<F.rank ∧
    Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h ∧
    L-k≤minimumExposure Y 7 ∧ 5*minimumExposure Y 7≤22+2*h := by
  intro Y k h L
  obtain ⟨_,exactPrice,rank,degree,_,_⟩ := minimal_rank_exact_source F paid
  have cap (v:F.X) := (degree v).trans_eq eight
  have pk := full_independent_set_le_matching F.G 8 (by decide) cap I stage.1 stage.2.1
  have top : diagonal F.n F.m (F.r+2)=9 := by omega
  have orig : widthAt F.n F.m F.r 9=h := by rw [←top];exact width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm
  obtain ⟨wide,cost,row⟩ := original_stage_width_and_cost F.G F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row
    (by decide : 0<8) cap I stage
  change widthAt F.n F.m F.r 9≤k at wide
  rw [orig] at wide
  have hp : 1≤h := (strict_eight_inventory F paid eight).1
  have live : 0<rowCount F.s F.t (F.r+k) := by change 0<F.s+F.t-1-(F.r+k);change matchingEdges F.G<F.s+F.t-1-F.r at rank;change k≤matchingEdges F.G at pk;omega
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by change F.s+F.t-1-(F.r+k)<F.s+F.t-1-F.r;change 0<F.s+F.t-1-(F.r+k) at live;omega
  have loss := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r k 8 top.le
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+8*k+widthAt F.n F.m F.r 9 at loss
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+8*k at cost
  rw [orig] at loss
  have excess : Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h := by omega
  have low (x) : Nat.card (Y.neighborSet x)≤7 := by
    have lt := complete_stage_lowers_cap F.G 8 I cap stage x
    change Nat.card (Y.neighborSet x)<8 at lt;omega
  have shifted := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r k 9
  rw [orig] at shifted
  have height := height_below_empty_column F.n F.m live (show widthAt F.n F.m (F.r+k) 9=0 by omega)
  have seven := smaller_row_seven_exposure_budget F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) F.rank
    row live smaller paid low (by omega)
  have col := widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 8 row (by decide)
  rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm] at col
  have needed := col.trans ((uniformEnvelope_le_deletion Y 7 (by decide)).trans (deletionBudget_le_minimumExposure Y 7 (by decide) low))
  exact ⟨wide,live,smaller,excess,needed,by omega⟩

#print axioms strict_eight_complete_stage
end JSP452Audit.StarHost
