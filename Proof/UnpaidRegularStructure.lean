import SmallAlphaComponentPays
import EquimatchableReserve
import ZhaoReservePrices
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] [Nonempty X]
/-- Any unpaid regular component has an actual independent triple and
all of its inclusion-maximal matchings reach the original maximum. -/
theorem unpaid_regular_structure (Q : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (reg : ∀x,Nat.card (Q.neighborSet x)=D) (crit : PerfectAfterEveryDeletion Q)
    (fail : envelopeReserve Q k < minimumExposure Q D) :
    (∃ S : Set X,S.ncard=3 ∧ Q.IsIndepSet S) ∧
      ∀ M : Q.Subgraph, M.IsMatching →
        (∀ N : Q.Subgraph,N.IsMatching → M≤N → M=N) → M.edgeSet.ncard=matchingEdges Q := by
  have rank := regular_factorCritical_exposure Q crit (Classical.choice ‹Nonempty X›) D reg
  have pay := (envelope_reserve_account Q D).2
  have stable := envelopeReserve_le_truncation Q D k (fun x => (reg x).le)
  have zero : baseReserve Q D=0 := by omega
  have miss : ¬NoIndependentTriple Q := fun small => (Nat.not_lt_of_ge (small_alpha_component_pays Q D k large reg crit small)) fail
  have eq : D-1+1=D := by omega
  exact ⟨independent_triple_vertex_set _ miss, fun M hm maximal =>
    zero_reserve_all_maximal_maximum Q (D-1) (by simpa [eq] using reg) crit (by simpa [eq] using zero) M hm maximal⟩
#print axioms unpaid_regular_structure
end JSP452Audit.StarHost
