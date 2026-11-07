import SurvivingColumnFirstOffset
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_complete_stage_shadow (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (I:Set F.X) (stage:CompleteDegreeStage F.G 6 I) :
    let k := I.ncard
    let h := highestWidth F.n F.m F.r
    let L := widthAt F.n F.m F.r 6
    let Y := F.G.induce Iᶜ
    h≤k ∧ Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h ∧
      3*(L-k)≤2*h+10 ∧
      (k<L → L-k≤minimumExposure Y 5 ∧ 5*minimumExposure Y 5≤2*h+2*(L-k)+10) := by
  intro k h L Y
  have src := minimal_rank_exact_source F paid
  have cap (v:F.X) := (src.2.2.2.1 v).trans_eq six
  obtain ⟨top,cost,row⟩ := original_stage_width_and_cost F.G F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.row
    (by decide : 0<6) cap I stage
  have head : diagonal F.n F.m (F.r+2)=7 := by omega
  have atTop : widthAt F.n F.m F.r 7=h := by rw [←head];exact width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm
  change widthAt F.n F.m F.r 7≤k at top
  have hk : h≤k := atTop ▸ top
  have hp : 1≤h := (strict_six_real_component_bounds F paid six).1
  have loss := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm F.r k 6 head.le
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+6*k+widthAt F.n F.m F.r 7 at loss
  have earlier := src.2.1
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+6*k at cost
  have excess : Y.edgeSet.ncard+1≤rowEnergy F.n F.m (F.r+k)+h := by omega
  refine ⟨hk,excess,?_⟩
  by_cases live : k<L
  · obtain ⟨positive,nextHead,width⟩ := shifted_live_six_has_exact_head F.hs F.ht F.n F.m F.hn F.hm top live
    have bound (v:↥(Iᶜ:Set F.X)) : Nat.card (Y.neighborSet v)≤5 := by
      have small := complete_stage_lowers_cap F.G 6 I cap stage v
      change Nat.card (Y.neighborSet v)<6 at small;omega
    change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) at row
    have current (v:↥(Iᶜ:Set F.X)) : Nat.card (Y.neighborSet v)≤diagonal F.n F.m ((F.r+k)+2)-1 := by rw [nextHead];exact bound v
    have exposed := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) positive row current).2
    rw [nextHead,width] at exposed
    change L-k≤minimumExposure Y 5 at exposed
    have smaller : rowCount F.s F.t (F.r+k)<F.rank := by
      have old := F.live
      change rowCount F.s F.t (F.r+k)<rowCount F.s F.t F.r
      dsimp [rowCount] at *;omega
    have price := universal_selector_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 5 F.rank row
      positive smaller paid bound nextHead.le
    rw [widthAt_shift F.hs F.ht F.n F.m F.hn F.hm] at price
    change (rowEnergy F.n F.m (F.r+k):ℤ)+max 0 (((5*(minimumExposure Y 5:ℤ)+1)/2-6)-((L-k:ℕ):ℤ))≤(Y.edgeSet.ncard:ℤ) at price
    have exactBound : 5*minimumExposure Y 5≤2*h+2*(L-k)+10 := by omega
    exact ⟨by omega,fun _ => ⟨exposed,exactBound⟩⟩
  · exact ⟨by omega,fun contradiction => (live contradiction).elim⟩

#print axioms strict_six_complete_stage_shadow
end JSP452Audit.StarHost
