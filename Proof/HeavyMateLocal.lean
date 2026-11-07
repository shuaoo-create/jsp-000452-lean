import NoThreeAugment
import MateAntineighborhood

namespace JSP452Audit.StarHost
open SimpleGraph

/-- An endpoint with at least two distinct neighbors omitted by the same
matching N, counted among the original vertices of H. -/
def holeHeavy {X : Type*} (H : SimpleGraph X) (N : H.Subgraph) (a : X) : Prop :=
  2 ≤ (H.neighborSet a ∩ N.vertsᶜ).ncard

/-- Choose an exposed neighbor different from any prescribed label. -/
theorem holeHeavy_exposed_neighbor_ne {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) {a : X} (heavy : holeHeavy H N a) (avoid : X) :
    ∃ x, x∉N.verts ∧ H.Adj x a ∧ x≠avoid := by
  have more : ({avoid} : Set X).ncard < (H.neighborSet a ∩ N.vertsᶜ).ncard := by
    rw [Set.ncard_singleton]
    unfold holeHeavy at heavy
    omega
  obtain ⟨x,neighbor,outside⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard more
  exact ⟨x,neighbor.2,(show H.Adj a x from neighbor.1).symm,
    fun eq => outside (Set.mem_singleton_iff.mpr eq)⟩

/-- Every heavy endpoint is covered by this maximum matching. -/
theorem holeHeavy_mem_verts {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) (matching : N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges H) {a : X} (heavy : holeHeavy H N a) :
    a∈N.verts := by
  obtain ⟨x,hole,xa,_⟩ := holeHeavy_exposed_neighbor_ne H N heavy a
  exact missed_neighbors_subset H N matching maximum hole xa

/-- A matched partner of a heavy endpoint has no edge to any exposed label.
If it reached y, a different exposed neighbor x of the heavy endpoint would
give a three-edge augmenting path on this same matched edge. -/
theorem holeHeavy_partner_mem_antineighborhood {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) (matching : N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges H) {a b : X}
    (heavy : holeHeavy H N a) (ab : N.Adj a b) :
    b∈mateAntineighborhood H N.vertsᶜ := by
  refine ⟨fun hole => hole (N.edge_vert ab.symm),?_⟩
  intro y exposed byEdge
  obtain ⟨x,hole,xa,distinct⟩ := holeHeavy_exposed_neighbor_ne H N heavy y
  exact no_three_augment H N matching maximum hole exposed distinct ab xa byEdge

/-- The partner guaranteed by the actual matching belongs to the common
antineighborhood of its exposed vertices. -/
theorem holeHeavy_exists_partner {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) (matching : N.IsMatching)
    (maximum : N.edgeSet.ncard=matchingEdges H) {a : X} (heavy : holeHeavy H N a) :
    ∃ b, N.Adj a b ∧ b∈mateAntineighborhood H N.vertsᶜ := by
  obtain ⟨b,ab,_⟩ := matching (holeHeavy_mem_verts H N matching maximum heavy)
  exact ⟨b,ab,holeHeavy_partner_mem_antineighborhood H N matching maximum heavy ab⟩

/-- Even when the two neighborhoods overlap, a distinct exposed neighbor
can be selected on each side. The two heavy endpoints need not be distinct. -/
theorem holeHeavy_distinct_exposed_neighbors {X : Type*} [Finite X]
    (H : SimpleGraph X) (N : H.Subgraph) {a c : X}
    (heavyA : holeHeavy H N a) (heavyC : holeHeavy H N c) :
    ∃ x y, x∉N.verts ∧ y∉N.verts ∧ x≠y ∧ H.Adj x a ∧ H.Adj c y := by
  obtain ⟨y,hy,yc,_⟩ := holeHeavy_exposed_neighbor_ne H N heavyC c
  obtain ⟨x,hx,xa,distinct⟩ := holeHeavy_exposed_neighbor_ne H N heavyA y
  exact ⟨x,y,hx,hy,distinct,xa,yc.symm⟩

#print axioms holeHeavy_exposed_neighbor_ne
#print axioms holeHeavy_mem_verts
#print axioms holeHeavy_partner_mem_antineighborhood
#print axioms holeHeavy_exists_partner
#print axioms holeHeavy_distinct_exposed_neighbors
end JSP452Audit.StarHost

