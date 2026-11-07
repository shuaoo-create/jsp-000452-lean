import TheWidthOneExposureFourRegionIsActuallyClosed
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_zero_odd_alternatives (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0) :
    Nonempty (ClosedTenFour F.G) ∨
    (highestWidth F.n F.m F.r=1 ∧ minimumExposure F.G 10=3 ∧ ∃(K:TenOuterCut F.G) (M:F.G.Subgraph),
      M.IsMatching ∧ M.edgeSet.ncard=matchingEdges F.G ∧ K.score=1 ∧ (exposedFull F.G M 10).ncard=3 ∧
      45≤K.support.ncard ∧ (F.G.induce K.support).edgeSet.ncard+1=5*K.support.ncard ∧
      ∃B:K.InnerBarrier,matchingEdges F.G=B.actualRoots.ncard+matchingEdges (F.G.induce B.residual)+
        matchingEdges (F.G.induce K.remainder) ∧ K.rootDefect B.residual≤2 ∧
        ∀x∈B.residual,∀y∈K.remainder,¬F.G.Adj x y) := by
  obtain ⟨K,M,hm,best,opt,wide,sat|exception⟩ := strict_ten_original_matching_endpoint F paid ten none
  · obtain ⟨est,_,_,_⟩ := sat
    have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
    by_cases two:K.score=2
    · exact Or.inl (score_two_closed_support K cap none M hm est two)
    · have small := K.small
      have pos := K.positive
      have hp := (strict_ten_inventory F paid ten).1
      have one : K.score=1 := by omega
      obtain ⟨B⟩ := K.inner_barrier_exists cap M hm est
      obtain ⟨_,rank,_⟩ := B.exact_region_matching_partition cap M hm best est
      obtain ⟨less,few⟩ := B.residual_original_defect cap none
      rcases K.orders_and_edges_by_score cap none with ⟨_,size,edges⟩|⟨wrong,_⟩
      · exact Or.inr ⟨by omega,by omega,K,M,hm,best,one,by omega,size,edges,B,rank,less.trans few,B.physical_partition.2.2.2.2⟩
      · omega
  · exact Or.inl (width_one_exposure_four_closed_support F paid ten none exception.1 exception.2.2)

theorem strict_ten_closed_four_exterior (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (C:ClosedTenFour F.G) :
    let P := matchingEdges (F.G.induce C.support)
    let O := F.G.induce C.supportᶜ
    let d := F.rank-matchingEdges F.G
    let q := F.t-F.r-P
    let k := F.s-F.r-P
    P+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤matchingEdges O ∧
    (F.G.induce C.support).edgeSet.ncard=10*P+20 ∧
    d+1≤q ∧ d+1≤k ∧ matchingEdges O+d+1=F.s+q ∧ matchingEdges O+d+1=F.t+k ∧
    (∀R:SimpleGraph ↥(C.supportᶜ:Set F.X),R≤O → (forest F.n).IsContained R ∨ q≤matchingEdges (O \ R)) ∧
    (∀R:SimpleGraph ↥(C.supportᶜ:Set F.X),R≤O → (forest F.m).IsContained R ∨ k≤matchingEdges (O \ R)) := by
  intro P O d q k
  have full (x) (hx:x∈C.support) : Nat.card (F.G.neighborSet x)=diagonal F.n F.m (F.r+2)-1 := (C.full x hx).trans ten.symm
  have lengths := strict_closed_union_lengths F paid C.support C.closed full
  have endpoints := strict_closed_union_endpoint_pair F paid C.support C.closed full
  have edge : (F.G.induce C.support).edgeSet.ncard=10*P+20 := by
    have zero : crossCount F.G C.support C.supportᶜ=0 := crossCount_of_no_edges _ _ _ (fun x hx y hy adj => hy (C.closed x hx y adj))
    have cost := incident_piece_edge_count F.G C.support
    have delete := root_deletion_cost F.G C.support
    have erasure := erase_internal_edge_count F.G C.supportᶜ
    rw [degree_sum_full F.G C.support 10 C.full] at delete
    have size := C.deficit
    change C.support.ncard=2*P+4 at size
    omega
  exact ⟨lengths.1,lengths.2,edge,endpoints⟩

#print axioms strict_ten_zero_odd_alternatives
#print axioms strict_ten_closed_four_exterior
end JSP452Audit.StarHost
