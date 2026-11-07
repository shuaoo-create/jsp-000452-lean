import ExactRankOfTheTenDegreePieceWithPorts
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ranks_of_complementary_induced_sets {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X) :
    matchingEdges (G.induce U)+matchingEdges (G.induce Uᶜ)≤matchingEdges G := by
  classical
  let join : ↥U ⊕ ↥Uᶜ → X := Sum.elim Subtype.val Subtype.val
  have inj : Function.Injective join := by
    rintro (a|a) (b|b) h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exact False.elim (b.property ((show a.val=b.val from h) ▸ a.property))
    · exact False.elim (a.property ((show a.val=b.val from h).symm ▸ b.property))
    · exact congrArg Sum.inr (Subtype.ext h)
  have mapAdj {a b:↥U ⊕ ↥Uᶜ} (edge:(G.induce U ⊕g G.induce Uᶜ).Adj a b) : G.Adj (join a) (join b) := by
    rcases a with a|a <;> rcases b with b|b
    · exact edge
    · exact False.elim (not_adj_sum_inl_inr a b edge)
    · exact False.elim (not_adj_sum_inl_inr b a edge.symm)
    · exact edge
  let copy : (G.induce U ⊕g G.induce Uᶜ).Copy G := { toHom := ⟨join,mapAdj⟩, injective' := inj }
  simpa only [matchingEdges_sumGraph] using rank_le_of_copy copy

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem whole_matching_partition (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (best:M.edgeSet.ncard=matchingEdges G) (attained:(exposedFull G M 10).ncard=K.score+2) :
    matchingEdges G=matchingEdges K.incidentPiece+(M.spanningCoe.induce K.supportᶜ).edgeSet.ncard ∧
    matchingEdges G≤matchingEdges K.incidentPiece+matchingEdges (G.induce K.supportᶜ) ∧
    matchingEdges K.incidentPiece+matchingEdges (G.induce K.supportᶜ)≤matchingEdges G+K.targetPorts := by
  have split := erase_internal_edge_count M.spanningCoe K.supportᶜ
  have inside := (K.global_optimum_inside_piece cap M hm attained).1
  have exactRank := K.incident_piece_rank cap M hm attained
  have out := edges_of_matching_inside_set M hm K.supportᶜ
  have lower := ranks_of_complementary_induced_sets G K.support
  change M.spanningCoe.edgeSet.ncard=matchingEdges G at best
  omega

theorem piece_size_and_fee (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (M:G.Subgraph) (hm:M.IsMatching) (attained:(exposedFull G M 10).ncard=K.score+2) :
    let P := (K.support.ncard-1)/2
    let eps := K.support.ncard-2*P
    let B := matchingEdges K.incidentPiece
    (eps=1 ∨ eps=2) ∧ K.support.ncard=2*P+eps ∧ B≤P ∧
    (K.score=1 → 22≤P) ∧ (K.score=2 → 27≤P) ∧
    K.incidentPiece.edgeSet.ncard+2=10*B+10*(P-B)+5*eps+K.score+K.allPorts := by
  intro P eps B
  have size := K.support_order_lower cap none
  have rank := K.incident_piece_rank cap M hm attained
  change B=matchingEdges (G.induce K.support)+K.targetPorts at rank
  have defic := (K.exact_support_matching_rank cap M hm attained).2.1
  change 2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+K.targetPorts=K.support.ncard at defic
  obtain ⟨fee,loss⟩ := K.true_piece_edge_fee cap none
  have ports := K.spanning_support_boundary G le_rfl
  change K.allPorts=crossCount G K.S K.supportᶜ+K.targetPorts at ports
  have pos := K.positive
  have sm := K.small
  dsimp only [P,eps];omega

theorem strict_ten_exterior_deficit (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenOuterCut F.G) (none:(oddRegularComponents F.G 10).ncard=0)
    (M:F.G.Subgraph) (hm:M.IsMatching) (best:M.edgeSet.ncard=matchingEdges F.G)
    (opt:(exposedFull F.G M 10).ncard=minimumExposure F.G 10)
    (attained:(exposedFull F.G M 10).ncard=K.score+2) :
    let d := F.rank-matchingEdges F.G
    let dY := F.rank-matchingEdges K.incidentPiece-matchingEdges (F.G.induce K.supportᶜ)
    d≤dY+K.targetPorts ∧ dY≤d ∧ 2≤dY ∧ (K.score=2 → 5≤dY) := by
  intro d dY
  have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq ten
  obtain ⟨_,a,b⟩ := K.whole_matching_partition cap M hm best attained
  have gap := minimal_strict_source_deficit F paid
  dsimp only at gap;rw [ten] at gap
  have loss := (K.true_piece_edge_fee cap none).2
  have ports := K.spanning_support_boundary F.G le_rfl
  change K.allPorts=crossCount F.G K.S K.supportᶜ+K.targetPorts at ports
  have pos := K.positive
  dsimp only [d,dY];omega
end TenOuterCut
#print axioms ranks_of_complementary_induced_sets
#print axioms TenOuterCut.whole_matching_partition
#print axioms TenOuterCut.piece_size_and_fee
#print axioms TenOuterCut.strict_ten_exterior_deficit
end JSP452Audit.StarHost
