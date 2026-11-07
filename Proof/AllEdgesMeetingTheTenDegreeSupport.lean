import MatchingRanksAfterDeletingWholeSetsOfSourceRoots
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem incident_piece_edge_count {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X) :
    (eraseInternal G Uᶜ).edgeSet.ncard=(G.induce U).edgeSet.ncard+crossCount G U Uᶜ := by
  have cost := root_deletion_cost G U
  have hand := JSP452Audit.StarHost.two_block_handshake G U
  have erasure := erase_internal_edge_count G Uᶜ
  omega

theorem edges_of_matching_palette {X:Type u} [Finite X] {G:SimpleGraph X} (M:G.Subgraph) (hm:M.IsMatching)
    (Q A:SimpleGraph X) (inside:Q≤M.spanningCoe) (sub:Q≤A) : Q.edgeSet.ncard≤matchingEdges A := by
  let L : A.Subgraph := {
    verts := {x|∃y,Q.Adj x y}
    Adj := Q.Adj
    adj_sub := fun h => sub h
    edge_vert := fun e => ⟨_,e⟩
    symm := Q.symm }
  have mat : L.IsMatching := by
    rintro x ⟨y,e⟩
    exact ⟨y,e,fun z h => hm.eq_of_adj_left (inside h) (inside e)⟩
  exact le_matchingEdges mat

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

def incidentPiece := eraseInternal G K.supportᶜ
noncomputable def targetPorts := crossCount G K.T K.supportᶜ
noncomputable def allPorts := crossCount G K.support K.supportᶜ

theorem true_piece_edge_fee (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    K.incidentPiece.edgeSet.ncard+2=5*K.support.ncard+K.score+K.allPorts ∧
      K.rootDefect K.S+K.rootDefect K.T+K.allPorts+2*K.score=4 := by
  have count := incident_piece_edge_count G K.support
  have inside := K.induced_support_edges cap none
  have loss := (K.exact_root_and_port_losses cap none).2.2.2
  rw [←K.support_boundary] at loss
  change (eraseInternal G K.supportᶜ).edgeSet.ncard+2=5*K.support.ncard+K.score+crossCount G K.support K.supportᶜ ∧ _
  exact ⟨by omega,loss⟩

theorem global_optimum_inside_piece (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    (eraseInternal M.spanningCoe K.supportᶜ).edgeSet.ncard=matchingEdges (G.induce K.support)+K.targetPorts ∧
      matchingEdges (G.induce K.support)+K.targetPorts≤matchingEdges K.incidentPiece := by
  let R := M.spanningCoe
  have count := incident_piece_edge_count R K.support
  rw [K.spanning_support_boundary R M.spanningCoe_le] at count
  have inside := (K.exact_support_matching_rank cap M hm attained).1
  obtain ⟨_,_,_,s,t,_⟩ := K.matching_endpoint_saturation cap M hm attained
  have ports := cross_count_color_partition G R M.spanningCoe_le K.T K.supportᶜ
  change crossCount R K.S K.supportᶜ=0 at s
  change crossCount (G \ R) K.T K.supportᶜ=0 at t
  change (R.induce K.support).edgeSet.ncard=matchingEdges (G.induce K.support) at inside
  rw [t,Nat.add_zero] at ports
  rw [s,Nat.zero_add,←ports,inside] at count
  have available := edges_of_matching_palette M hm (eraseInternal R K.supportᶜ) K.incidentPiece
    (eraseInternal_le _ _) (fun _ _ e => ⟨M.spanningCoe_le e.1,e.2⟩)
  exact ⟨count,count ▸ available⟩
end TenOuterCut

#print axioms incident_piece_edge_count
#print axioms edges_of_matching_palette
#print axioms TenOuterCut.true_piece_edge_fee
#print axioms TenOuterCut.global_optimum_inside_piece
end JSP452Audit.StarHost
