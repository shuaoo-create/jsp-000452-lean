import PortedReserve
import EnvelopeComponentSum
import ZhaoExceptionalReserve
import SmallComplementFacts
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An unpaid actual component must itself be regular and factor-critical.
No relabelled surrogate or sum component is substituted here. -/
theorem unpaid_component_regular (G : SimpleGraph X) (D k : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (c : G.ConnectedComponent)
    (unpaid : envelopeReserve c.toSimpleGraph k < minimumExposure c.toSimpleGraph D) :
    (∀x : c.supp,Nat.card (G.neighborSet x.val)=D) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph := by
  by_contra missing
  have noReg := (noOriginalRegularCritical_component_original_iff G c D).mpr missing
  have pay := (ported_reserve c.toSimpleGraph D k pos
    (fun x => (component_degree_eq G c x).trans_le (cap x.val)) noReg).2
  exact (Nat.not_lt_of_ge pay) unpaid

/-- Every unpaid component at degree at least three lies in the exact
unresolved regular class: even degree, an independent triple, all maximal
matchings maximum, and none of the already paid exceptional models. -/
theorem unpaid_component_obstruction (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (c : G.ConnectedComponent)
    (unpaid : envelopeReserve c.toSimpleGraph k < minimumExposure c.toSimpleGraph D) :
    (∀x : c.supp,Nat.card (G.neighborSet x.val)=D) ∧
    PerfectAfterEveryDeletion c.toSimpleGraph ∧
    Even D ∧ 4≤D ∧
    (∃ I : Set c.supp,I.ncard=3 ∧ c.toSimpleGraph.IsIndepSet I) ∧
    (∀ M : c.toSimpleGraph.Subgraph,M.IsMatching →
      (∀ N : c.toSimpleGraph.Subgraph,N.IsMatching → M≤N → M=N) →
      M.edgeSet.ncard=matchingEdges c.toSimpleGraph) ∧
    (∀d : ℕ,2≤d → ¬Nonempty (c.toSimpleGraph ≃g zhaoGraph d)) ∧
    ¬Nonempty (c.toSimpleGraph ≃g (zhaoGraph 2)ᶜ) := by
  classical
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  obtain ⟨reg,crit⟩ := unpaid_component_regular G D k (by omega) cap c unpaid
  have internal (x : c.supp) : Nat.card (c.toSimpleGraph.neighborSet x)=D :=
    (component_degree_eq G c x).trans (reg x)
  have order := factorCritical_order_rank c.toSimpleGraph crit
    (Classical.choice ‹Nonempty c.supp›)
  have odd : Odd (Nat.card c.supp) := ⟨matchingEdges c.toSimpleGraph,by omega⟩
  have even := regular_even_on_odd c.toSimpleGraph D odd internal
  have parity := Nat.even_iff.mp even
  obtain ⟨ind,eq⟩ := unpaid_regular_structure c.toSimpleGraph D k large internal crit unpaid
  obtain ⟨models,comp⟩ := unpaid_regular_not_exceptional c.toSimpleGraph D k internal crit unpaid
  exact ⟨reg,crit,even,by omega,ind,eq,models,comp⟩

#print axioms unpaid_component_regular
#print axioms unpaid_component_obstruction
end JSP452Audit.StarHost
