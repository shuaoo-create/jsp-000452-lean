import ClosedUnionExteriorEndpoints
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_closed_union_endpoint_pair (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (U : Set F.X) (closed : ∀v∈U,∀w,F.G.Adj v w → w∈U)
    (full : ∀v∈U,Nat.card (F.G.neighborSet v)=diagonal F.n F.m (F.r+2)-1) :
    let P := matchingEdges (F.G.induce U)
    let O := F.G.induce Uᶜ
    let d := F.rank-matchingEdges F.G
    let q := F.t-F.r-P
    let k := F.s-F.r-P
    d+1≤q ∧ d+1≤k ∧ matchingEdges O+d+1=F.s+q ∧ matchingEdges O+d+1=F.t+k ∧
    (∀R:SimpleGraph ↥(Uᶜ : Set F.X),R≤O → (forest F.n).IsContained R ∨ q≤matchingEdges (O \ R)) ∧
    (∀R:SimpleGraph ↥(Uᶜ : Set F.X),R≤O → (forest F.m).IsContained R ∨ k≤matchingEdges (O \ R)) := by
  intro P O d q k
  have lens := (strict_closed_union_lengths F paid U closed full).1
  change P+F.r+d+1≤min F.s F.t at lens
  have rs := lens.trans (Nat.min_le_left _ _)
  have rt := lens.trans (Nat.min_le_right _ _)
  have split := closed_union_matching_split F.G U closed
  change matchingEdges F.G=P+matchingEdges O at split
  have less := (minimal_rank_exact_source F paid).2.2.1
  have account : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have total : F.rank+F.r+1=F.s+F.t := by
    change rowCount F.s F.t F.r+F.r+1=F.s+F.t
    unfold rowCount
    omega
  refine ⟨by dsimp [q];omega,by dsimp [k];omega,by dsimp [q];omega,by dsimp [k];omega,?_,?_⟩
  · exact closed_union_exterior_endpoint F.G U closed F.hs (by omega) F.n F.m F.pn F.pm F.row
  · exact closed_union_exterior_endpoint F.G U closed F.ht (by omega) F.m F.n F.pm F.pn
      (swap_positive_forcing_row F.G _ _ F.row)

#print axioms strict_closed_union_endpoint_pair
end JSP452Audit.StarHost
