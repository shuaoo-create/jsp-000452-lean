import ExactFeeOnTheSamePortExteriorWhenTheLastVertexHasDegreeEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Removing one matching that covers all maximum-degree vertices gives the
edge bound for a bipartite graph, including graphs with isolated vertices. -/
theorem bipartite_edges_le_cap_times_rank {X:Type u} [Finite X] (G:SimpleGraph X) (A:Set X) (D:ℕ)
    (cap:∀v,Nat.card (G.neighborSet v)≤D) (bip:∀x y,G.Adj x y → (x∈A ↔ y∉A)) :
    G.edgeSet.ncard≤D*matchingEdges G := by
  induction D generalizing G with
  | zero =>
    have empty:G=⊥ := by
      ext x y
      refine ⟨fun e => ?_,False.elim⟩
      have live : Nonempty (G.neighborSet x) := ⟨⟨y,e⟩⟩
      have pos := Nat.card_pos (α:=G.neighborSet x)
      have := cap x
      omega
    simp [empty]
  | succ d ih =>
    obtain ⟨M,hm,below⟩ := remainder_via_bipartite_cut G A (d+1) (by omega) cap (fun x _ y e => bip x y e)
    let H := G \ M.spanningCoe
    have small := ih H (fun x => below x) (fun x y e => bip x y e.1)
    have rank := rank_le_of_copy (SimpleGraph.Copy.ofLE H G sdiff_le)
    have mono := Nat.mul_le_mul_left d rank
    have count := le_matchingEdges hm
    have total := eraseMatching_edge_count M
    change H.edgeSet.ncard+M.edgeSet.ncard=G.edgeSet.ncard at total
    rw [Nat.succ_mul];omega

#print axioms bipartite_edges_le_cap_times_rank
end JSP452Audit.StarHost
