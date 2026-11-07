import AlternatingFive
import HeavyMateLocal
import ExceptionalEdgeCount
import MateHoleTransport
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- If the residual anti-neighborhood is a clique, two distinct vertices
cannot each have at least two uncovered neighbors. Their matched partners
would be adjacent, yielding a forbidden length-five augmenting path. -/
theorem heavy_endpoint_unique (H : SimpleGraph X) (N : H.Subgraph)
    (matching : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (clique : H.IsClique (mateAntineighborhood H N.vertsᶜ))
    {a c : X} (ha : holeHeavy H N a) (hc : holeHeavy H N c) : a=c := by
  by_contra different
  obtain ⟨b,ab,hb⟩ := holeHeavy_exists_partner H N matching maximum ha
  obtain ⟨d,cd,hd⟩ := holeHeavy_exists_partner H N matching maximum hc
  have bdNe : b≠d := fun eq => different (matching.eq_of_adj_right (eq ▸ ab) cd)
  have bd := clique hb hd bdNe
  obtain ⟨x,y,hx,hy,xy,xa,cy⟩ := holeHeavy_distinct_exposed_neighbors H N ha hc
  exact no_five_augment H N matching maximum hx hy xy ab cd.symm xa bd cy

theorem heavy_endpoint_count (H : SimpleGraph X) (N : H.Subgraph)
    (matching : N.IsMatching) (maximum : N.edgeSet.ncard=matchingEdges H)
    (clique : H.IsClique (mateAntineighborhood H N.vertsᶜ)) :
    {a | holeHeavy H N a}.ncard≤1 := by
  apply (Set.ncard_le_one (Set.toFinite _)).mpr
  exact fun a ha c hc => heavy_endpoint_unique H N matching maximum clique ha hc

/-- On the original near-perfect-matching decomposition, at most one
surviving label has two original W-neighbors; at most one actual residual
matching edge has such an endpoint. This proves the at-most part of Zhao
Lemma 2.5(iv) on the unpaid route, without any existence assertion. -/
theorem actual_mate_exception_at_most_one (Q : SimpleGraph X) (D : ℕ)
    (pos : 0<D) (reg : ∀x,Nat.card (Q.neighborSet x)=D)
    (crit : PerfectAfterEveryDeletion Q) (zero : baseReserve Q D=0)
    (I : Set X) (ind : Q.IsIndepSet I)
    (max : ∀S : Set X,Q.IsIndepSet S → S.ncard≤I.ncard)
    (v : X) (vi : v∈I) (M : Q.Subgraph) (hm : M.IsMatching) (expose : M.verts={x|x≠v}) :
    let N := restrictedOutsideMatching Q I M
    let W := independentMateLabels Q I v M
    {a : ↥(Iᶜ : Set X) | 2≤(Q.neighborSet a.val ∩ W).ncard}.ncard≤1 ∧
    {e : Sym2 ↥(Iᶜ : Set X) | e∈N.edgeSet ∧ ∃a∈e,2≤(Q.neighborSet a.val ∩ W).ncard}.ncard≤1 := by
  intro N W
  let H := Q.induce Iᶜ
  obtain ⟨matching,maximum,clique⟩ := residual_mate_clique Q D pos reg crit zero I ind max v vi M hm expose
  obtain ⟨_,_,labels,_,_⟩ := independent_mate_barrier Q D pos reg crit zero I ind v vi M hm expose
  have count (a : ↥(Iᶜ : Set X)) :
      holeHeavy H N a ↔ 2≤(Q.neighborSet a.val ∩ W).ncard := by
    unfold holeHeavy
    rw [original_mate_neighbor_count Q I N W labels a]
  have points : {a : ↥(Iᶜ : Set X) | 2≤(Q.neighborSet a.val ∩ W).ncard}.ncard≤1 := by
    simpa only [←count] using heavy_endpoint_count H N matching maximum clique
  exact ⟨points,matching_edges_with_endpoint_le_one H N matching _ points⟩

#print axioms heavy_endpoint_unique
#print axioms heavy_endpoint_count
#print axioms actual_mate_exception_at_most_one
end JSP452Audit.StarHost
