import OriginalTenDegreeMatchingEndpointOrTheWidthOneException
open private JSP452Audit.StarHost.two_block_handshake from RootDeletionCost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem split_covered_and_uncovered {X:Type u} [Finite X] (A V:Set X) :
    (A∩V).ncard+(A\V).ncard=A.ncard := by
  have un : (A∩V)∪(A\V)=A := by ext x;by_cases h:x∈V <;> simp [h]
  have dis : Disjoint (A∩V) (A\V) := Set.disjoint_left.mpr (fun _ a b => b.2 a.2)
  rw [←Set.ncard_union_eq dis,un]

theorem uncovered_disjoint_union {X:Type u} [Finite X] (A B V:Set X) (dis:Disjoint A B) :
    ((A∪B)\V).ncard=(A\V).ncard+(B\V).ncard := by
  have eq : (A∪B)\V=(A\V)∪(B\V) := by ext x;simp only [Set.mem_diff,Set.mem_union];tauto
  rw [eq,Set.ncard_union_eq (dis.mono Set.diff_subset Set.diff_subset)]

namespace TenOuterCut
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenOuterCut G)

theorem unmatched_partition (M:G.Subgraph) :
    (K.support\M.verts).ncard=(K.S\M.verts).ncard+(K.T\M.verts).ncard+(K.core\M.verts).ncard := by
  have dis : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  change ((K.roots∪K.core)\M.verts).ncard=_
  rw [uncovered_disjoint_union K.roots K.core M.verts dis,uncovered_disjoint_union K.S K.T M.verts K.apart]

theorem core_uncovered (cap:∀x,Nat.card (G.neighborSet x)≤10) (M:G.Subgraph) :
    K.core\M.verts=K.core∩exposedFull G M 10 := by
  ext x
  exact ⟨fun hx => ⟨hx.1,hx.2,K.core_is_full cap x hx.1⟩,fun hx => ⟨hx.1,hx.2.1⟩⟩

theorem spanning_support_boundary (H:SimpleGraph X) (sub:H≤G) :
    crossCount H K.support K.supportᶜ=crossCount H K.S K.supportᶜ+crossCount H K.T K.supportᶜ := by
  have away : crossCount H K.supportᶜ K.core=0 := by
    apply crossCount_of_no_edges
    intro x hx y hy edge
    obtain root|inside := regionCore_neighbor G K.roots K.pieces hy (sub edge.symm)
    · obtain ⟨v,_,rfl⟩ := root;exact hx (Or.inl v.property)
    · exact hx (Or.inr inside)
  have apart : Disjoint K.roots K.core := disjoint_compl_right.mono_right K.core_outside
  rw [crossCount_swap H K.support K.supportᶜ]
  change crossCount H K.supportᶜ (K.roots∪K.core)=_
  rw [cut_cross_union_right H K.supportᶜ K.roots K.core apart,away,Nat.add_zero,
    cut_cross_union_right H K.supportᶜ K.S K.T K.apart,crossCount_swap H K.supportᶜ K.S,crossCount_swap H K.supportᶜ K.T]

theorem internal_matching_edge_deficit (M:G.Subgraph) (hm:M.IsMatching) :
    let R := M.spanningCoe
    2*(R.induce K.support).edgeSet.ncard+(K.support\M.verts).ncard+
      crossCount R K.S K.supportᶜ+crossCount R K.T K.supportᶜ=K.support.ncard := by
  intro R
  have hand := JSP452Audit.StarHost.two_block_handshake R K.support
  have split := K.spanning_support_boundary R M.spanningCoe_le
  rw [split] at hand
  have count := matching_degree_sum_eq_covered M hm K.support
  change originalDegreeSum R K.support=_ at count
  have whole := split_covered_and_uncovered K.support M.verts
  omega
end TenOuterCut
#print axioms split_covered_and_uncovered
#print axioms uncovered_disjoint_union
#print axioms TenOuterCut.unmatched_partition
#print axioms TenOuterCut.core_uncovered
#print axioms TenOuterCut.spanning_support_boundary
#print axioms TenOuterCut.internal_matching_edge_deficit
end JSP452Audit.StarHost
