import ExposureComponentSum
import UnpaidOriginalComponent
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Global exposure is paid whenever each actual component pays. -/
theorem envelope_reserve_of_component_pay (G : SimpleGraph X) (D k : ℕ)
    (pay : ∀c:G.ConnectedComponent,minimumExposure c.toSimpleGraph D≤envelopeReserve c.toSimpleGraph k) :
    minimumExposure G D≤envelopeReserve G k := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  rw [minimumExposure_component_total G D]
  exact (Finset.sum_le_sum (fun c _ => pay c)).trans (envelopeReserve_component_sum_le G k)

/-- All nonregular-or-noncritical components are now discharged. The remaining
assumption is explicitly and only about the actual regular critical ones. -/
theorem envelope_reserve_of_regular_component_pay (G : SimpleGraph X) (D k : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (regularPay : ∀c:G.ConnectedComponent,
      (∀x:c.supp,Nat.card (G.neighborSet x.val)=D) →
      PerfectAfterEveryDeletion c.toSimpleGraph →
      minimumExposure c.toSimpleGraph D≤envelopeReserve c.toSimpleGraph k) :
    minimumExposure G D≤envelopeReserve G k := by
  apply envelope_reserve_of_component_pay G D k
  intro c
  by_contra fail
  have unpaid := Nat.lt_of_not_ge fail
  obtain ⟨reg,crit⟩ := unpaid_component_regular G D k pos cap c unpaid
  exact fail (regularPay c reg crit)

/-- If the general reserve inequality fails, an actual original connected
component witnesses that failure, not just a hypothetical replacement graph. -/
theorem exists_unpaid_original_component (G : SimpleGraph X) (D k : ℕ)
    (unpaid : envelopeReserve G k < minimumExposure G D) :
    ∃c:G.ConnectedComponent,envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have strict := (envelopeReserve_component_sum_le G k).trans_lt unpaid
  rw [minimumExposure_component_total G D] at strict
  obtain ⟨c,_,hc⟩ := Finset.exists_lt_of_sum_lt strict
  exact ⟨c,hc⟩

/-- Complete original-component reduction of the unresolved reserve branch.
The only remaining components are connected even-regular critical graphs
with the stated exact constraints. This is a reduction, not a classification. -/
theorem unpaid_graph_regular_obstruction (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (unpaid : envelopeReserve G k < minimumExposure G D) :
    ∃c:G.ConnectedComponent,
      envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D ∧
      (∀x:c.supp,Nat.card (G.neighborSet x.val)=D) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph ∧
      Even D ∧ 4≤D ∧
      (∃ I : Set c.supp,I.ncard=3 ∧ c.toSimpleGraph.IsIndepSet I) ∧
      (∀ M : c.toSimpleGraph.Subgraph,M.IsMatching →
        (∀ N : c.toSimpleGraph.Subgraph,N.IsMatching → M≤N → M=N) →
        M.edgeSet.ncard=matchingEdges c.toSimpleGraph) ∧
      (∀d : ℕ,2≤d → ¬Nonempty (c.toSimpleGraph ≃g zhaoGraph d)) ∧
      ¬Nonempty (c.toSimpleGraph ≃g (zhaoGraph 2)ᶜ) := by
  obtain ⟨c,hc⟩ := exists_unpaid_original_component G D k unpaid
  exact ⟨c,hc,unpaid_component_obstruction G D k large cap c hc⟩

/-- A concrete structural family is fully paid without invoking any unproved
classification. It includes arbitrary disjoint combinations of ported
components, all small-independence regular components, and both model families. -/
theorem reserve_of_resolved_regular_components (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (resolved : ∀c:G.ConnectedComponent,
      (∀x:c.supp,Nat.card (G.neighborSet x.val)=D) →
      PerfectAfterEveryDeletion c.toSimpleGraph →
      NoIndependentTriple c.toSimpleGraph ∨
      (∃d:ℕ,2≤d ∧ Nonempty (c.toSimpleGraph ≃g zhaoGraph d)) ∨
      Nonempty (c.toSimpleGraph ≃g (zhaoGraph 2)ᶜ)) :
    minimumExposure G D≤envelopeReserve G k := by
  by_contra fail
  obtain ⟨c,hc,reg,crit,_,_,ind,_,models,comp⟩ :=
    unpaid_graph_regular_obstruction G D k large cap (Nat.lt_of_not_ge fail)
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  rcases resolved c reg crit with small | ⟨d,hd,iso⟩ | iso
  · have pay := small_alpha_component_pays c.toSimpleGraph D k large
      (fun x => (component_degree_eq G c x).trans (reg x)) crit small
    exact (Nat.not_lt_of_ge pay) hc
  · exact models d hd iso
  · exact comp iso

#print axioms envelope_reserve_of_component_pay
#print axioms envelope_reserve_of_regular_component_pay
#print axioms exists_unpaid_original_component
#print axioms unpaid_graph_regular_obstruction
#print axioms reserve_of_resolved_regular_components
end JSP452Audit.StarHost
