import AllEdgesMeetingTheTenDegreeSupport
namespace JSP452Audit.StarHost.TenOuterCut
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem source_port_cost_for_any_matching (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    :
    2*(M.spanningCoe.induce K.support).edgeSet.ncard+2*crossCount M.spanningCoe K.S K.supportᶜ+
      K.score+2+K.rootDefect K.T+K.targetPorts+2*(K.S\M.verts).ncard≤K.support.ncard := by
  let R := M.spanningCoe
  let N := G \ R
  have original := actual_degree_sum_of_palette G R M.spanningCoe_le K.T
  have covered : originalDegreeSum R K.T=(K.T∩M.verts).ncard := matching_degree_sum_eq_covered M hm K.T
  change _+originalDegreeSum N K.T=_ at original
  have ledger := K.matching_token_account cap M hm
  change K.pieces.ncard+crossCount G K.T K.S+2*(R.induce K.S).edgeSet.ncard+2*(N.induce K.T).edgeSet.ncard+
    crossCount R K.S K.supportᶜ+crossCount N K.T K.supportᶜ≤(K.S∩M.verts).ncard+originalDegreeSum N K.T+(K.core∩exposedFull G M 10).ncard at ledger
  have split := cross_count_color_partition G R M.spanningCoe_le K.T K.supportᶜ
  change crossCount G K.T K.supportᶜ=crossCount R K.T K.supportᶜ+crossCount N K.T K.supportᶜ at split
  have hand := K.internal_matching_edge_deficit M hm
  change 2*(R.induce K.support).edgeSet.ncard+_+crossCount R K.S K.supportᶜ+crossCount R K.T K.supportᶜ=_ at hand
  have core := K.core_uncovered cap M
  rw [←core] at ledger
  have s := split_covered_and_uncovered K.S M.verts
  have t := split_covered_and_uncovered K.T M.verts
  have missed := K.unmatched_partition M
  have capT := degree_sum_le_cap G K.T 10 (fun x _ => cap x)
  have im := K.imbalance
  have z := K.actual
  rw [uniform_factor_cut_on_original] at z
  change (K.pieces.ncard:ℤ)+(crossCount G K.T K.S:ℤ)-3*(K.S.ncard:ℤ)-7*(K.T.ncard:ℤ)=(K.score:ℤ) at z
  change 2*(R.induce K.support).edgeSet.ncard+2*crossCount R K.S K.supportᶜ+K.score+2+K.rootDefect K.T+crossCount G K.T K.supportᶜ+2*(K.S\M.verts).ncard≤_
  dsimp only [rootDefect]
  omega


theorem incident_piece_rank (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) (hm:M.IsMatching)
    (attained:(exposedFull G M 10).ncard=K.score+2) :
    matchingEdges K.incidentPiece=matchingEdges (G.induce K.support)+K.targetPorts := by
  apply le_antisymm _ (K.global_optimum_inside_piece cap M hm attained).2
  obtain ⟨L,matchL,best⟩ := exists_maximum_matching K.incidentPiece
  let A : G.Subgraph := {
    verts := L.verts
    Adj := L.Adj
    adj_sub := fun e => (L.adj_sub e).1
    edge_vert := L.edge_vert
    symm := L.symm }
  have matchA : A.IsMatching := matchL
  have fixed : eraseInternal A.spanningCoe K.supportᶜ=A.spanningCoe := by
    ext x y
    exact ⟨fun e => e.1,fun e => ⟨e,(L.adj_sub e).2⟩⟩
  have tally := incident_piece_edge_count A.spanningCoe K.support
  rw [fixed,K.spanning_support_boundary A.spanningCoe A.spanningCoe_le] at tally
  have bound := K.source_port_cost_for_any_matching cap A matchA
  have actual := (K.exact_support_matching_rank cap M hm attained).2.1
  have split := cross_count_color_partition G A.spanningCoe A.spanningCoe_le K.T K.supportᶜ
  change K.targetPorts=_ at split
  change A.spanningCoe.edgeSet.ncard=matchingEdges K.incidentPiece at best
  change 2*matchingEdges (G.induce K.support)+K.score+2+K.rootDefect K.T+K.targetPorts=_ at actual
  omega

#print axioms source_port_cost_for_any_matching
#print axioms incident_piece_rank
end JSP452Audit.StarHost.TenOuterCut
