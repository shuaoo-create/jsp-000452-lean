import PayExposureEightFromFourActualUnselectedBlocks
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_costed_eight_residual (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (S:Set F.X) (w:ℕ)
    (cap:∀v,Nat.card ((F.G.induce Sᶜ).neighborSet v)≤8)
    (cost:F.G.edgeSet.ncard=(F.G.induce Sᶜ).edgeSet.ncard+9*S.ncard+w)
    (signed:widthAt F.n F.m F.r 10-w≤(38+2*highestWidth F.n F.m F.r)/7-2) :
    let Y := F.G.induce Sᶜ
    let h := highestWidth F.n F.m F.r
    minimumExposure Y 8≤max 4 ((h-1+((38+2*h)/7-2)+16)/3) := by
  classical
  intro Y h
  let k := S.ncard
  let L := widthAt F.n F.m F.r 10
  let v := h-1+((38+2*h)/7-2)
  have top : diagonal F.n F.m (F.r+2)=11 := by omega
  have liveL : 0<L := (width_positive_at_first_offset F.hs F.ht F.n F.m F.hn F.hm).mpr ⟨F.live,by omega⟩
  have feasible : admits_matching_remainder Y 9 := by
    refine ⟨⊥,fun _ a => a.elim,?_⟩
    intro x;rw [Subgraph.spanningCoe_bot,sdiff_bot];exact cap x
  have width := original_width_le_deletion F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r 9 F.row (by decide)
  have done : L≤k := width.trans (deletionBudget_le_of_witness F.G 9 S feasible)
  have smaller : rowCount F.s F.t (F.r+k)<F.rank := by
    have live := F.live
    change rowCount F.s F.t (F.r+k)<rowCount F.s F.t F.r;dsimp [rowCount] at live ⊢;omega
  have next := row_delete_set F.G S _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) at next
  have tax := prefix_at_two_top_columns F.hs F.ht F.n F.m F.hn F.hm 9 top k
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+k)+9*k+L+h at tax
  have old := (minimal_rank_exact_source F paid).2.1
  change F.G.edgeSet.ncard=Y.edgeSet.ncard+9*k+w at cost
  change L-w≤(38+2*h)/7-2 at signed
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  have excess : Y.edgeSet.ncard≤rowEnergy F.n F.m (F.r+k)+v := by dsimp [v];omega
  change minimumExposure Y 8≤max 4 ((v+16)/3)
  by_cases few:minimumExposure Y 8≤4
  · exact few.trans (le_max_left _ _)
  by_cases live:0<rowCount F.s F.t (F.r+k)
  · have empty := widthAt_shift F.hs F.ht F.n F.m F.hn F.hm F.r k 10
    change widthAt F.n F.m (F.r+k) 10=L-k at empty
    have ht := height_below_empty_column F.n F.m live (show widthAt F.n F.m (F.r+k) 10=0 by omega)
    have price := eight_exposure_four_piece_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) F.rank
      next live smaller.le paid cap (by omega) (by omega)
    have wlim := (widthAt_le_uniformEnvelope F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) 9 next (by decide)).trans
      ((uniformEnvelope_le_deletion Y 8 (by decide)).trans (deletionBudget_le_minimumExposure Y 8 (by decide) cap))
    omega
  · have dead : rowCount F.s F.t (F.r+k)=0 := by omega
    have energy : rowEnergy F.n F.m (F.r+k)=0 := by simp [rowEnergy,dead]
    rw [energy,Nat.zero_add] at excess
    have bound := exposed_vertex_incidence_bound Y 8
    omega

#print axioms strict_ten_costed_eight_residual
end JSP452Audit.StarHost
