import BothOriginalForestsAreLongOnTheActualTenDegreePartition
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- The support and its incident edges use labels of the same host as the
partition. The extra matching edges are the actual exterior target ports. -/
structure TenPortSupport {X:Type u} [Finite X] (G:SimpleGraph X) (R:TenBlockPartition G) (h:ℕ) where
  support : Set X
  targetPorts : ℕ
  targetDefect : ℕ
  orderFloor : 34+11*h≤support.ncard
  regionRank : matchingEdges (eraseInternal G supportᶜ)=R.roots.ncard+R.capacity
  portRank : matchingEdges (eraseInternal G supportᶜ)=matchingEdges (G.induce support)+targetPorts
  order : 2*matchingEdges (G.induce support)+h+2+targetDefect+targetPorts=support.ncard
  edges : (G.induce support).edgeSet.ncard+1=5*support.ncard
  ports : targetPorts≤crossCount G support supportᶜ
  defect : targetDefect+crossCount G support supportᶜ≤2

namespace TenPortSupport
theorem of_cut {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G) (A:K.InnerBarrier)
    (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0)
    (M:G.Subgraph) (hm:M.IsMatching) (best:M.edgeSet.ncard=matchingEdges G)
    (sat:(exposedFull G M 10).ncard=K.score+2) (one:K.score=1) :
    ∃R:TenBlockPartition G, ∃W:TenPortSupport G R 1,
      W.support=K.support ∧ W.targetPorts=K.targetPorts ∧ W.targetDefect=K.rootDefect K.T ∧
      R.epsilon≤2 ∧ 3+R.epsilon≤R.eta ∧ R.eta≤5 := by
  obtain ⟨R,roots,core,rest,eta,low,high⟩ := TenBlockPartition.from_outer_cut K A cap none M hm best sat one
  have balance := (A.exact_region_matching_partition cap M hm best sat).1
  have region : matchingEdges (eraseInternal G K.supportᶜ)=R.roots.ncard+R.capacity := by
    change matchingEdges K.incidentPiece=R.roots.ncard+matchingEdges (G.induce R.core)
    rw [roots,core];exact balance
  have orders := K.support_order_lower cap none
  have size := (K.exact_support_matching_rank cap M hm sat).2.1
  change 2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+K.targetPorts=K.support.ncard at size
  have boundary := K.spanning_support_boundary G le_rfl
  change crossCount G K.support K.supportᶜ=_+K.targetPorts at boundary
  have debt := (K.true_piece_edge_fee cap none).2
  change K.rootDefect K.S+K.rootDefect K.T+crossCount G K.support K.supportᶜ+2*K.score=4 at debt
  have fee := K.induced_support_edges cap none
  exact ⟨R,⟨K.support,K.targetPorts,K.rootDefect K.T,by omega,region,K.incident_piece_rank cap M hm sat,
     by omega,by omega,by omega,by omega⟩,rfl,rfl,rfl,by omega,by omega,by omega⟩

#print axioms of_cut
end TenPortSupport
end JSP452Audit.StarHost
