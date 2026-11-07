import RootDeletionCost
import Mathlib.Combinatorics.SimpleGraph.Clique

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
/-- Removing P preserves the incident original edges at every selected vertex. -/
theorem neighborSet_after_disjoint_piece (G P : SimpleGraph X) (U : Set X)
    (away : ∀ ⦃x y⦄, P.Adj x y → x ∉ U) {x : X} (hx : x ∈ U) :
    (G \ P).neighborSet x = G.neighborSet x := by
  ext y
  exact ⟨fun h => h.1,fun h => ⟨h,fun edge => away edge hx⟩⟩

/-- All erased piece edges and all D incidences per independent selected vertex
give distinct edge deletions on the original host. -/
theorem selected_edge_saving (G P : SimpleGraph X) (U : Set X) (D : ℕ)
    (sub : P ≤ G) (indep : G.IsIndepSet U) (full : ∀ v ∈ U, Nat.card (G.neighborSet v) = D)
    (away : ∀ ⦃x y⦄, P.Adj x y → x ∉ U) :
    G.edgeSet.ncard = ((G \ P).induce Uᶜ).edgeSet.ncard + P.edgeSet.ncard + D * U.ncard := by
  have left : (G \ P).edgeSet.ncard + P.edgeSet.ncard = G.edgeSet.ncard := by
    rw [edgeSet_sdiff]
    exact Set.ncard_sdiff_add_ncard_of_subset (edgeSet_subset_edgeSet.mpr sub)
  have unchanged (v : X) (hv : v ∈ U) : Nat.card ((G \ P).neighborSet v) = D := by
    rw [neighborSet_after_disjoint_piece G P U away hv,full v hv]
  have internal : (G \ P).induce U = ⊥ := by
    ext x y
    refine ⟨fun h => ?_,False.elim⟩
    have edge : G.Adj x.val y.val := h.1
    exact indep x.property y.property edge.ne edge
  have deleted := root_deletion_cost (G \ P) U
  rw [internal,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero,
    degree_sum_full (G \ P) U D unchanged] at deleted
  omega

#print axioms neighborSet_after_disjoint_piece
#print axioms selected_edge_saving
end JSP452Audit.StarHost
