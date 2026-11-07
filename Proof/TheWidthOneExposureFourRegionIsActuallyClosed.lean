import TotalOriginalDegreeDefectOfTheTenDegreeResidual
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

structure ClosedTenFour {X:Type u} [Finite X] (G:SimpleGraph X) where
  support : Set X
  closed : ∀x∈support,∀y,G.Adj x y → y∈support
  full : ∀x∈support,Nat.card (G.neighborSet x)=10
  deficit : support.ncard=2*matchingEdges (G.induce support)+4

theorem width_one_exposure_four_closed_support (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (none:(oddRegularComponents F.G 10).ncard=0)
    (one:highestWidth F.n F.m F.r=1) (four:minimumExposure F.G 10=4) : Nonempty (ClosedTenFour F.G) := by
  obtain ⟨K⟩ := degreeRegion_exists F.G 10
  have cap (v:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have lower := K.weight_identity cap
  have dom := positivePieces_dominate F.G K.barrier K.pieces 10
  change edgeSurplus (F.G.induce K.core) 10≤edgeSurplus (F.G.induce K.positiveCore) 10 at dom
  have upper := strict_even_positive_weight_ceiling F paid 5 (by decide) ten K
  change edgeSurplus (F.G.induce K.positiveCore) 10≤(highestWidth F.n F.m F.r:ℤ)-1+5*(5-1)+
    ((oddRegularComponents F.G 10).ncard:ℤ) at upper
  rw [one,none] at upper
  rw [four] at lower
  have zero : rootShortfall F.G K.roots 10=0 := by omega
  have empty : crossCount F.G K.roots K.rest=0 := by omega
  obtain ⟨closed,full,size⟩ := zero_loss_full_closed_region K cap zero empty
  rw [←ordinary_region_internal_root_rank F.G 10 K,four] at size
  exact ⟨⟨_,closed,full,size⟩⟩

theorem score_two_closed_support {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)
    (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (M:G.Subgraph) (hm:M.IsMatching) (attained:(exposedFull G M 10).ncard=K.score+2) (two:K.score=2) :
    Nonempty (ClosedTenFour G) := by
  rcases K.orders_and_edges_by_score cap none with wrong|⟨_,_,_,full,closed⟩
  · omega
  · have d := (K.exact_support_matching_rank cap M hm attained).2.1
    have loss := (K.true_piece_edge_fee cap none).2
    have ports := K.spanning_support_boundary G le_rfl
    change K.allPorts=crossCount G K.S K.supportᶜ+K.targetPorts at ports
    change 2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+K.targetPorts=K.support.ncard at d
    exact ⟨⟨_,closed,full,by omega⟩⟩

#print axioms width_one_exposure_four_closed_support
#print axioms score_two_closed_support
end JSP452Audit.StarHost
