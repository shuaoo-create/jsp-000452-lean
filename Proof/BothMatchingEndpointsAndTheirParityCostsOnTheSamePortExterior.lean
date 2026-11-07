import TheTwoCompleteForestTailsOnTheActualPortExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_exterior_matching_endpoints (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ}
    (W:TenPortSupport F.G K h) (deep:h+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t) :
    let O := W.outside
    let B := W.rank
    let d := F.rank-B-matchingEdges O
    let p := F.t-F.r-B
    let q := F.s-F.r-B
    h+1≤d ∧ B+matchingEdges O+d=F.rank ∧
      matchingEdges O+d+1=F.s+p ∧ matchingEdges O+d+1=F.t+q ∧
      ForestMatchingEndpoint O F.n p ∧ ForestMatchingEndpoint O F.m q ∧
      2*(d+∑i,(F.n i-1)/2)≤p ∧ 2*(d+∑i,(F.m i-1)/2)≤q := by
  intro O B d p q
  obtain ⟨lower,upper,gap,le,priced⟩ := W.exterior_rank_window F.rank deep
  change h+1≤d at priced
  have lengthS := length.trans (Nat.min_le_left _ _)
  have lengthT := length.trans (Nat.min_le_right _ _)
  change B+F.r+_+1≤F.s at lengthS
  change B+F.r+_+1≤F.t at lengthT
  have accr : B+matchingEdges O+d=F.rank := by dsimp only [d] at priced ⊢;omega
  have good : F.rank=F.s+F.t-1-F.r := rfl
  have a : matchingEdges O+d+1=F.s+p := by dsimp only [p];omega
  have b : matchingEdges O+d+1=F.t+q := by dsimp only [q];omega
  have positiveP : 0<p := by dsimp only [p];omega
  have positiveQ : 0<q := by dsimp only [q];omega
  have cover : O≤O⊔(⊥:SimpleGraph ↥(W.supportᶜ:Set F.X)) := le_sup_left
  have mrow := W.complete_blue_tail F.n F.m F.hm F.pn F.pm F.row
  have nrow := W.complete_blue_tail F.m F.n F.hn F.pm F.pn (swap_positive_forcing_row _ _ _ F.row)
  have left := edge_palette_forest_endpoint O O ⊥ le_rfl cover F.hs (by dsimp only [B] at *;omega : F.r<F.t-W.rank)
    F.n (remainingDemand F.m W.rank) (remainingDemand_positive F.m F.pm _) mrow
  have right := edge_palette_forest_endpoint O O ⊥ le_rfl cover F.ht (by dsimp only [B] at *;omega : F.r<F.s-W.rank)
    F.m (remainingDemand F.n W.rank) (remainingDemand_positive F.n F.pn _) nrow
  rw [matchingEdges_bot,Nat.sub_zero] at left right
  have lp : ForestMatchingEndpoint O F.n p := by convert left using 1 <;> dsimp only [p,B] <;> omega
  have rp : ForestMatchingEndpoint O F.m q := by convert right using 1 <;> dsimp only [q,B] <;> omega
  exact ⟨priced,accr,a,b,lp,rp,endpoint_forest_parity_cost O F.n F.pn lp (by omega) positiveP
    (positive_endpoint_rank O F.hs F.n F.pn lp) a,endpoint_forest_parity_cost O F.m F.pm rp (by omega) positiveQ
    (positive_endpoint_rank O F.ht F.m F.pm rp) b⟩

#print axioms ten_port_exterior_matching_endpoints
end JSP452Audit.StarHost
