import CriticalBarrier
import BarrierExitCount
import OddComponentExit
import ExitEquivalence
namespace JSP452Audit.StarHost
open SimpleGraph

theorem matched_exit_equiv {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (tight : IsTightBarrier G S) (M : G.Subgraph) (hm : M.IsMatching)
    (max : M.edgeSet.ncard=matchingEdges G)
    (odd : ∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp)) :
    ∃ e : (G.induce Sᶜ).ConnectedComponent ≃ (↥S ⊕ ↥(M.vertsᶜ : Set X)),
      ∀ c z, IsBarrierExit G S M c z ↔ e c=z := by
  apply matched_exit_equiv_of_count G S M hm _ (barrier_exit_count G S tight M hm max odd)
  intro c
  obtain ⟨x,hx,miss|⟨s,hs,edge⟩⟩ := odd_component_exit G S c M hm (odd c)
  · exact ⟨.inr ⟨x.val,miss⟩,x,hx,rfl⟩
  · exact ⟨.inl ⟨s,hs⟩,x,hx,edge⟩

/-- The barrier is fixed before the maximum matching is chosen. Each residual
component has a genuine near-perfect matching with any prescribed missing vertex,
and for each global maximum matching its matched/exposed exit is unique and exhaustive. -/
theorem original_matching_decomposition {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ S : Set X, IsTightBarrier G S ∧
      (∀ c : (G.induce Sᶜ).ConnectedComponent, Odd (Nat.card c.supp) ∧
        PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp)) ∧
      ∀ M : G.Subgraph, M.IsMatching → M.edgeSet.ncard=matchingEdges G →
        ∃ e : (G.induce Sᶜ).ConnectedComponent ≃ (↥S ⊕ ↥(M.vertsᶜ : Set X)),
          ∀ c z, IsBarrierExit G S M c z ↔ e c=z := by
  obtain ⟨S,tight,localData⟩ := exists_critical_barrier G
  exact ⟨S,tight,localData,fun M hm max => matched_exit_equiv G S tight M hm max (fun c => (localData c).1)⟩

#print axioms matched_exit_equiv
#print axioms original_matching_decomposition
end JSP452Audit.StarHost