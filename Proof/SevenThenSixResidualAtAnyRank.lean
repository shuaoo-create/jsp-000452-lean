import ImprovedSixDegreeResidualPrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_eight_costed_six_residual (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (S:Set F.X) (w:ℕ)
    (cap:∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤6)
    (cost:F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+7*S.ncard+w)
    (signed:widthAt F.n F.m F.r 8-w≤(22+2*highestWidth F.n F.m F.r)/5-2) :
    let Y := F.G.induce Sᶜ
    let h := highestWidth F.n F.m F.r
    minimumExposure Y 6≤max 3 ((h-1+((22+2*h)/5-2)+9)/2) := by
  classical
  intro Y h
  let k := S.ncard
  let L := widthAt F.n F.m F.r 8
  let v := h-1+((22+2*h)/5-2)
  have top : diagonal F.n F.m (F.r+2)=9 := by omega
  have liveL : 0<L := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  have feasible : admits_matching_remainder Y 7 := by
    refine ⟨⊥,fun _ a => a.elim,?_⟩
    intro x;rw [Subgraph.spanningCoe_bot,sdiff_bot];exact cap x
  have width := original_width_le_deletion F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r 7 F.row (by decide)
  have done : L≤k := width.trans (deletionBudget_le_of_witness F.G 7 S feasible)
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by
    have live := F.live
    change rowCount F.s F.t (F.r+k)<rowCount F.s F.t F.r;dsimp [rowCount] at live ⊢;omega
  have next := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) at next
  have tax := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 7 top k
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+7*k+L+h at tax
  have old := (minimal_rank_exact_source F paid).2.1
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+7*k+w at cost
  change L-w≤(22+2*h)/5-2 at signed
  have hp : 1≤h := (strict_eight_inventory F paid eight).1
  have excess : Y.edgeSet.ncard≤rowEnergy F.n F.m (F.r+k)+v := by dsimp [v];omega
  change minimumExposure Y 6≤max 3 ((v+9)/2)
  by_cases few:minimumExposure Y 6≤3
  · exact few.trans (le_max_left _ _)
  by_cases live:0<rowCount F.s F.t (F.r+k)
  · have empty := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r k 8
    change widthAt F.n F.m (F.r+k) 8=L-k at empty
    have ht := height_below_empty_column F.n F.m live (show widthAt F.n F.m (F.r+k) 8=0 by omega)
    have price := six_exposure_three_piece_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) F.rank
      next live smaller.le paid cap (by omega) (by omega)
    have wlim := (widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 7 next (by decide)).trans
      ((uniformEnvelope_le_deletion Y 6 (by decide)).trans (deletionBudget_le_minimumExposure Y 6 (by decide) cap))
    omega
  · have dead : rowCount F.s F.t (F.r+k)=0 := by omega
    have energy : rowEnergy F.n F.m (F.r+k)=0 := by simp [rowEnergy,dead]
    rw [energy,Nat.zero_add] at excess
    have bound := exposed_vertex_incidence_bound Y 6
    omega

#print axioms strict_eight_costed_six_residual
end JSP452Audit.StarHost
