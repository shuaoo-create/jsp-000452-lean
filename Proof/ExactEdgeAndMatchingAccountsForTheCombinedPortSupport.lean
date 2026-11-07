import TheStrongLengthsUseTheActualIncidentEdgeCapacity
namespace JSP452Audit.StarHost.TenPortSupport
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {R:TenBlockPartition G} {h:ℕ} (W:TenPortSupport G R h)
abbrev piece := eraseInternal G W.supportᶜ
abbrev outside := G.induce W.supportᶜ
noncomputable abbrev rank := matchingEdges W.piece
noncomputable abbrev half := (W.support.ncard-1)/2
noncomputable abbrev parity := W.support.ncard-2*W.half
noncomputable abbrev portCount := crossCount G W.support W.supportᶜ
noncomputable abbrev fee := W.piece.edgeSet.ncard-10*W.rank

theorem size_and_fee (positive:1≤h) :
    W.targetPorts≤W.portCount ∧ W.portCount≤2 ∧ (W.parity=1 ∨ W.parity=2) ∧
    W.support.ncard=2*W.half+W.parity ∧ W.rank≤W.half ∧ 22≤W.half ∧ (2≤h → 27≤W.half) ∧
    W.piece.edgeSet.ncard=10*W.rank+W.fee ∧
    W.fee+5*W.targetPorts=5*h+9+5*W.targetDefect+W.portCount ∧ 5*h+1≤W.fee ∧
    W.fee+1=10*(W.half-W.rank)+5*W.parity+W.portCount := by
  have rank := W.portRank
  change W.rank=matchingEdges (G.induce W.support)+W.targetPorts at rank
  have orders := W.order
  have min := W.orderFloor
  have few := W.defect
  have bound := W.ports
  have edges := W.edges
  have total := incident_piece_edge_count G W.support
  change W.piece.edgeSet.ncard=(G.induce W.support).edgeSet.ncard+crossCount G W.support W.supportᶜ at total
  dsimp only [half,parity,fee,portCount]
  omega

theorem exterior_rank_window (N:ℕ) (d:N-matchingEdges G≥h+3) :
    let old := N-matchingEdges G
    let new := N-W.rank-matchingEdges W.outside
    matchingEdges G≤W.rank+matchingEdges W.outside ∧ W.rank+matchingEdges W.outside≤matchingEdges G+W.targetPorts ∧
    old≤new+W.targetPorts ∧ new≤old ∧ h+1≤new := by
  intro old new
  have cover := rank_of_two_edge_colours G W.piece (G \ W.piece) (by
    intro x y e;by_cases cut:W.piece.Adj x y
    · exact Or.inl cut
    · exact Or.inr ⟨e,cut⟩)
  change matchingEdges G≤W.rank+matchingEdges (G \ eraseInternal G W.supportᶜ) at cover
  rw [rank_of_internal_edges] at cover
  change matchingEdges G≤W.rank+matchingEdges W.outside at cover
  have dis := ranks_of_complementary_induced_sets G W.support
  change matchingEdges (G.induce W.support)+matchingEdges W.outside≤matchingEdges G at dis
  have rank := W.portRank
  change W.rank=matchingEdges (G.induce W.support)+W.targetPorts at rank
  have upper := W.defect
  have charged := W.ports
  dsimp only [old,new];omega

#print axioms size_and_fee
#print axioms exterior_rank_window
end JSP452Audit.StarHost.TenPortSupport
