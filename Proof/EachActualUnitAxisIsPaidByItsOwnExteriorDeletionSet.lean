import TheActualWholePieceMenuCannotStopAtDegreeNine
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_port_axis_uses_cut (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ}
    (W:TenPortSupport F.G K h) (deep:h+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (j:ℕ) (positive:0<j) (C:Set ↥(W.supportᶜ:Set F.X))
    (cut:∀v,Nat.card ((W.outside.induce Cᶜ).neighborSet v)<j)
    (axis:∃x y,WinsHeight F.n F.m F.r j x y ∧ (x=1 ∨ y=1)) :
    widthAt F.n F.m F.r j≤W.rank+C.ncard := by
  let P := W.rank
  let L := widthAt F.n F.m F.r j
  have sr := length.trans (Nat.min_le_left _ _)
  have tr := length.trans (Nat.min_le_right _ _)
  change P+F.r+_+1≤F.s at sr
  change P+F.r+_+1≤F.t at tr
  obtain ⟨_,_,_,_,na,mb,_⟩ := ten_port_exterior_matching_endpoints F W deep length
  have cap (v) : Nat.card ((W.outside.induce Cᶜ).neighborSet v)≤j-1 := by have := cut v;omega
  have id : j-1+1=j := by omega
  obtain ⟨x,y,⟨_,_,ht,rx,byh,win⟩,unit⟩ := axis
  change L≤P+C.ncard
  rcases unit with rfl|rfl
  · have same : y=j := by omega
    subst y
    rw [original_threshold_one F.n F.pn] at win
    change L=F.s+originalThresholdCount F.m j-1-F.r at win
    have price := endpoint_threshold_stage W.outside F.m F.pm mb (by change 0<F.s-F.r-P;omega) C cap (id.symm ▸ byh)
    rw [id] at price
    change F.s-F.r-P-1+originalThresholdCount F.m j≤C.ncard at price;omega
  · have same : x=j := by omega
    subst x
    rw [original_threshold_one F.m F.pm] at win
    change L=originalThresholdCount F.n j+F.t-1-F.r at win
    have price := endpoint_threshold_stage W.outside F.n F.pn na (by change 0<F.t-F.r-P;omega) C cap (id.symm ▸ rx)
    rw [id] at price
    change F.t-F.r-P-1+originalThresholdCount F.n j≤C.ncard at price;omega

#print axioms ten_port_axis_uses_cut
end JSP452Audit.StarHost
