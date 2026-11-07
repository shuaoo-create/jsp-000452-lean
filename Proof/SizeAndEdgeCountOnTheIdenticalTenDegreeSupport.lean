import OrderOfTheTenDegreeTwoPortPieces
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem original_degree_sum_of_disjoint_union {X:Type u} [Finite X] (G:SimpleGraph X) (A B:Set X)
    (dis:Disjoint A B) : originalDegreeSum G (A∪B)=originalDegreeSum G A+originalDegreeSum G B := by
  classical
  have un : (A∪B).toFinite.toFinset=A.toFinite.toFinset∪B.toFinite.toFinset := by ext x;simp
  have apart : Disjoint A.toFinite.toFinset B.toFinite.toFinset :=
    Finset.disjoint_left.mpr (fun x a b => Set.disjoint_left.mp dis (A.toFinite.mem_toFinset.mp a) (B.toFinite.mem_toFinset.mp b))
  dsimp only [originalDegreeSum];rw [un,Finset.sum_union apart]

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem support_boundary : crossCount G K.support K.supportᶜ=crossCount G K.supportᶜ K.roots := by
  have away : crossCount G K.supportᶜ K.core=0 := by
    apply crossCount_of_no_edges
    intro x hx y hy edge
    obtain root|inside := regionCore_neighbor G K.roots K.pieces hy edge.symm
    · obtain ⟨v,_,rfl⟩ := root;exact hx (Or.inl v.property)
    · exact hx (Or.inr inside)
  have apart : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  rw [crossCount_swap G K.support K.supportᶜ]
  change crossCount G K.supportᶜ (K.roots∪K.core)=_
  rw [cut_cross_union_right G K.supportᶜ K.roots K.core apart,away,Nat.add_zero]

theorem induced_support_edges (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    (G.induce K.support).edgeSet.ncard+2=5*K.support.ncard+K.score := by
  have balance := (K.exact_root_and_port_losses cap none).2.2.2
  dsimp only [rootDefect] at balance
  have ds := degree_sum_le_cap G K.S 10 (fun x _ => cap x)
  have dt := degree_sum_le_cap G K.T 10 (fun x _ => cap x)
  have apart : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  have card : K.support.ncard=K.S.ncard+K.T.ncard+K.core.ncard := by
    change (K.roots∪K.core).ncard=_;rw [Set.ncard_union_eq apart,Set.ncard_union_eq K.apart]
  have roots := original_degree_sum_of_disjoint_union G K.S K.T K.apart
  have all := original_degree_sum_of_disjoint_union G K.roots K.core apart
  change originalDegreeSum G K.support=originalDegreeSum G K.roots+originalDegreeSum G K.core at all
  change originalDegreeSum G K.roots=_ at roots
  rw [roots,degree_sum_full G K.core 10 (K.core_is_full cap)] at all
  have hand := JSP452Audit.StarHost.two_block_handshake G K.support
  rw [K.support_boundary,all] at hand
  omega

theorem orders_and_edges_by_score (cap:∀x,Nat.card (G.neighborSet x)≤10) (none:(oddRegularComponents G 10).ncard=0) :
    (K.score=1 ∧ 45≤K.support.ncard ∧ (G.induce K.support).edgeSet.ncard+1=5*K.support.ncard) ∨
    (K.score=2 ∧ 56≤K.support.ncard ∧ (G.induce K.support).edgeSet.ncard=5*K.support.ncard ∧
      (∀x∈K.support,Nat.card (G.neighborSet x)=10) ∧ (∀x∈K.support,∀y,G.Adj x y → y∈K.support)) := by
  have fee := K.induced_support_edges cap none
  have size := K.support_order_lower cap none
  have pos := K.positive
  have hi := K.small
  by_cases one:K.score=1
  · exact Or.inl ⟨one,by omega,by omega⟩
  · have losses := (K.exact_root_and_port_losses cap none).2.2.2
    have full := K.roots_full_of_zero_loss cap (by omega) (by omega)
    exact Or.inr ⟨by omega,by omega,by omega,fun x mem => mem.elim (full x) (K.core_is_full cap x),
      K.support_closed_of_no_external_root_edge (by omega)⟩
end TenOuterCut

#print axioms original_degree_sum_of_disjoint_union
#print axioms TenOuterCut.support_boundary
#print axioms TenOuterCut.induced_support_edges
#print axioms TenOuterCut.orders_and_edges_by_score
end JSP452Audit.StarHost
