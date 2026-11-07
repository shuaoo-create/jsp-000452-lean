import DeletionBudget
import TutteJoin

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}

/-- Each actual vertex deletion admits an actual perfect matching. -/
def PerfectAfterEveryDeletion (G : SimpleGraph X) : Prop :=
  ∀ v : X, ∃ M : (G.induce {x | x ≠ v}).Subgraph, M.IsPerfectMatching

/-- Lift a perfect matching off v back along the inclusion. Its vertices
are exactly the old labels other than v, and it has maximum possible size. -/
theorem lift_perfect_off_vertex_maximum [Finite X] (G : SimpleGraph X) (v : X)
    (M : (G.induce {x | x ≠ v}).Subgraph) (perf : M.IsPerfectMatching) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N.verts = {x | x ≠ v} ∧
      N.edgeSet.ncard = matchingEdges G := by
  let e := SimpleGraph.Embedding.induce (G := G) {x | x ≠ v}
  let N := M.map e.toHom
  have hn : N.IsMatching := perf.1.map e.toHom e.injective
  have verts : N.verts = {x | x ≠ v} := by
    ext x
    constructor
    · rintro ⟨w,_,rfl⟩
      exact w.property
    · intro hx
      let w : {x : X // x ≠ v} := ⟨x,hx⟩
      exact ⟨w,perf.2 w,rfl⟩
  have pairCount := matching_vertices_eq_twice_edges hn
  have supportCount : N.verts.ncard = Nat.card X - 1 := by
    have complement : {x : X | x ≠ v} = ({v} : Set X)ᶜ := by ext; simp
    rw [verts,complement,Set.ncard_compl,Set.ncard_singleton]
  obtain ⟨K,hK,largest⟩ := exists_maximum_matching G
  have bound := Set.ncard_le_ncard (Set.subset_univ K.verts)
  rw [Set.ncard_univ,matching_vertices_eq_twice_edges hK,largest] at bound
  have lo := le_matchingEdges hn
  exact ⟨N,hn,verts,by omega⟩

theorem factorCritical_delete_rank [Finite X] (G : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion G) (v : X) :
    matchingEdges (G.induce {x | x ≠ v}) = matchingEdges G := by
  obtain ⟨M,perf⟩ := crit v
  obtain ⟨N,hn,verts,largest⟩ := lift_perfect_off_vertex_maximum G v M perf
  apply matchingEdges_delete_eq_of_avoiding G v
  exact ⟨N,hn,largest,by rw [verts]; exact fun h => h rfl⟩

/-- A low vertex can be the sole unmatched vertex of a maximum matching.
Consequently no full-degree vertex has to be exposed. -/
theorem factorCritical_peak_exposure_zero [Finite X] (G : SimpleGraph X) (D : ℕ)
    (crit : PerfectAfterEveryDeletion G) (y : X) (low : Nat.card (G.neighborSet y) < D) :
    minimumExposure G D = 0 := by
  obtain ⟨M,perf⟩ := crit y
  obtain ⟨N,hn,verts,largest⟩ := lift_perfect_off_vertex_maximum G y M perf
  have empty : exposedFull G N D = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have miss : v ∉ N.verts := hv.1
    have full : Nat.card (G.neighborSet v) = D := hv.2
    rw [verts] at miss
    have vy : v = y := Classical.not_not.mp miss
    subst v
    omega
  have bound := minimumExposure_le G D N hn largest
  rw [empty,Set.ncard_empty] at bound
  exact Nat.eq_zero_of_le_zero bound

theorem factorCritical_peak_budget_zero [Finite X] (G : SimpleGraph X) (D : ℕ)
    (pos : 0 < D) (bound : ∀ v, Nat.card (G.neighborSet v) ≤ D)
    (crit : PerfectAfterEveryDeletion G) (y : X) (low : Nat.card (G.neighborSet y) < D) :
    deletionBudget G D = 0 := by
  have upper := deletionBudget_le_minimumExposure G D pos bound
  rw [factorCritical_peak_exposure_zero G D crit y low] at upper
  exact Nat.eq_zero_of_le_zero upper

#print axioms lift_perfect_off_vertex_maximum
#print axioms factorCritical_delete_rank
#print axioms factorCritical_peak_exposure_zero
#print axioms factorCritical_peak_budget_zero
end JSP452Audit.StarHost
