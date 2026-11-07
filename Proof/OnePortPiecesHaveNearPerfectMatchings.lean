import EveryCountedPieceCostsOne
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem edges_of_matching_inside_set {X:Type*} [Finite X] {G:SimpleGraph X} (M:G.Subgraph) (hm:M.IsMatching)
    (U:Set X) : (M.spanningCoe.induce U).edgeSet.ncard≤matchingEdges (G.induce U) := by
  let Q := M.spanningCoe.induce U
  let N : (G.induce U).Subgraph := {
    verts := {x|∃y,Q.Adj x y}
    Adj := Q.Adj
    adj_sub := fun e => M.adj_sub e
    edge_vert := fun {x y} e => ⟨y,e⟩
    symm := Q.symm }
  have matchN : N.IsMatching := by
    intro v hv
    obtain ⟨y,e⟩ := hv
    exact ⟨y,e,fun z edge => Subtype.ext (hm.eq_of_adj_left edge e)⟩
  exact le_matchingEdges matchN

theorem matching_edges_fit_order {X:Type*} [Finite X] (G:SimpleGraph X) : 2*matchingEdges G≤Nat.card X := by
  obtain ⟨M,hm,best⟩ := exists_maximum_matching G
  have bound := Set.ncard_le_ncard (Set.subset_univ M.verts)
  rw [matching_vertices_eq_twice_edges hm,best,Set.ncard_univ] at bound
  exact bound

namespace NineOriginalCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:NineOriginalCut G)

theorem one_port_actual_inner_matching (cap:∀x,Nat.card (G.neighborSet x)≤9) (few:minimumExposure G 9≤4)
    (gap:K.S.ncard=K.T.ncard+1) (pos:1≤K.eta) (M:G.Subgraph) (hm:M.IsMatching)
    (optimal:(exposedFull G M 9).ncard=minimumExposure G 9)
    (c:↥K.blocks) (one:c∈K.onePortBlocks) :
    let U := K.labels c
    2*(M.spanningCoe.induce U).edgeSet.ncard+1=U.ncard ∧
    (M.spanningCoe.induce U).edgeSet.ncard=matchingEdges (G.induce U) ∧
    U.ncard=2*matchingEdges (G.induce U)+1 ∧ 5≤matchingEdges (G.induce U) := by
  intro U
  have oneUse := K.matching_use_equals_one cap few gap pos M hm optimal c
  have localEq := (K.matching_use_local cap M hm c).2
  have zero : crossCount G U K.T=0 := one.2
  have split := cross_count_color_partition G M.spanningCoe M.spanningCoe_le U K.T
  have none : crossCount M.spanningCoe U K.T=0 := by omega
  change 2*(M.spanningCoe.induce U).edgeSet.ncard+K.matchingUse M c=
    U.ncard+crossCount G U K.T-2*crossCount M.spanningCoe U K.T at localEq
  rw [oneUse,zero,none] at localEq
  have hit : 2*(M.spanningCoe.induce U).edgeSet.ncard+1=U.ncard := by simpa using localEq
  have reach := edges_of_matching_inside_set M hm U
  have fit := matching_edges_fit_order (G.induce U)
  change 2*matchingEdges (G.induce U)≤U.ncard at fit
  have same := Nat.card_congr (cutPieceVertexEquiv G K.barrier c.val)
  change Nat.card c.val.supp=U.ncard at same
  have size := (K.actual_one_port_order cap c one).2
  exact ⟨hit,by omega,by omega,by omega⟩

#print axioms one_port_actual_inner_matching
end NineOriginalCut
#print axioms edges_of_matching_inside_set
#print axioms matching_edges_fit_order
end JSP452Audit.StarHost
