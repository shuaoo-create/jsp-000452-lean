import ACompleteForestRowAfterErasingTheActualEdgePiece
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {K:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G K h)

noncomputable abbrev steps (r:ℕ) := W.rank-(r+1)

theorem rank_lower : 1≤W.rank := by
  have eq := W.order
  have low := W.orderFloor
  have sub := W.ports
  have total := W.defect
  have rank := W.portRank
  change W.rank=_ at rank
  omega

theorem whole_piece_rank_progress (F:StrictFamily.{u}) {K:TenBlockPartition F.G} {h:ℕ} (W:TenPortSupport F.G K h)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t) (deep:1≤F.rank-matchingEdges F.G) :
    let k := W.steps F.r
    let shift := k+W.rank
    W.rank≤F.r+k+1 ∧ 0<shift ∧ shift<F.rank ∧
      0<rowCount F.s F.t (F.r+shift) ∧ rowCount F.s F.t (F.r+shift)<F.rank := by
  intro k shift
  have left := length.trans (Nat.min_le_left _ _)
  have right := length.trans (Nat.min_le_right _ _)
  have pos := W.rank_lower
  dsimp only [shift,k,steps,StrictFamily.rank,rowCount] at *
  omega

theorem whole_piece_cost (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (V:Set ↥(W.supportᶜ:Set F.X)) (size:V.ncard=W.steps F.r) :
    let O := W.outside
    let Y := O.induce Vᶜ
    let k := V.ncard+W.rank
    0<rowCount F.s F.t (F.r+k) ∧ rowCount F.s F.t (F.r+k)<F.rank ∧
      ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) ∧
      O.edgeSet.ncard+W.fee+1≤Y.edgeSet.ncard+10*V.ncard+highestWidth F.n F.m F.r := by
  intro O Y k
  have deficit := (minimal_strict_source_deficit F paid).2.2
  obtain ⟨fit,_,_,pos,smaller⟩ := whole_piece_rank_progress F W length (by omega)
  have shifted : k=W.steps F.r+W.rank := by dsimp only [k];rw [size]
  have row := W.whole_piece_menu _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row V (size.symm ▸ fit)
  have current : ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (F.r+k) := by
    simpa only [k,Nat.add_assoc] using row
  have low : rowCount F.s F.t (F.r+k)<F.rank := shifted.symm ▸ smaller
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm Y (F.r+k) current low
  have profile := prefix_column_tax F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.r k F.live
  rw [ten] at profile
  have book := W.size_and_fee (strict_ten_inventory F paid ten).1
  have split := erase_internal_edge_count F.G W.supportᶜ
  change F.G.edgeSet.ncard=W.piece.edgeSet.ncard+O.edgeSet.ncard at split
  have fee : W.piece.edgeSet.ncard=10*W.rank+W.fee := book.2.2.2.2.2.2.2.1
  have strict := F.strict
  exact ⟨shifted.symm ▸ pos,low,current,by dsimp only [k] at *;omega⟩

#print axioms rank_lower
#print axioms whole_piece_rank_progress
#print axioms whole_piece_cost
end JSP452Audit.StarHost.TenPortSupport
