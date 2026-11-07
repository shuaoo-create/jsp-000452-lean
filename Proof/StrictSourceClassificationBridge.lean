import ActualRowReservePrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- A global minimum strict source either has the stronger actual rank deficit,
or contains an unpaid connected even-regular factor-critical component.
This is the precise unresolved alternative, with all original labels retained. -/
theorem strict_source_deficit_or_regular_obstruction
    (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    let D := diagonal F.n F.m (F.r+2)-1
    matchingEdges F.G+minimumExposure F.G D+1≤F.rank ∨
    ∃c:F.G.ConnectedComponent,
      envelopeReserve c.toSimpleGraph D<minimumExposure c.toSimpleGraph D ∧
      (∀x:c.supp,Nat.card (F.G.neighborSet x.val)=D) ∧
      PerfectAfterEveryDeletion c.toSimpleGraph ∧ Even D ∧ 4≤D := by
  intro D
  have large : 3≤D := strict_source_degree_at_least_three F paid
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have height : diagonal F.n F.m (F.r+2)≤D+1 := by dsimp [D] at *;omega
  rcases strict_row_deficit_or_unpaid_component F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
      F.G F.r D D F.row height F.strict with h | ⟨c,hc⟩
  · exact Or.inl h
  · obtain ⟨reg,crit,even,four,_⟩ := unpaid_component_obstruction F.G D D large cap c hc
    exact Or.inr ⟨c,hc,reg,crit,even,four⟩

/-- On the already resolved actual component classes the stronger deficit is
unconditional, including arbitrary combinations and arbitrary list tails. -/
theorem strict_source_deficit_of_resolved_components
    (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (resolved : let D := diagonal F.n F.m (F.r+2)-1
      ∀c:F.G.ConnectedComponent,
      (∀x:c.supp,Nat.card (F.G.neighborSet x.val)=D) →
      PerfectAfterEveryDeletion c.toSimpleGraph →
      NoIndependentTriple c.toSimpleGraph ∨
      (∃d:ℕ,2≤d ∧ Nonempty (c.toSimpleGraph ≃g zhaoGraph d)) ∨
      Nonempty (c.toSimpleGraph ≃g (zhaoGraph 2)ᶜ)) :
    let D := diagonal F.n F.m (F.r+2)-1
    matchingEdges F.G+minimumExposure F.G D+1≤F.rank := by
  intro D
  have large : 3≤D := strict_source_degree_at_least_three F paid
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have height : diagonal F.n F.m (F.r+2)≤D+1 := by dsimp [D] at *;omega
  have cost := reserve_of_resolved_regular_components F.G D D large cap resolved
  exact strict_row_of_envelope_payment F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    F.G F.r D D F.row height cost F.strict

/-- The partial reserve theorem now produces a concrete alternative directly
from failure of the original unbounded-list conjecture. -/
theorem original_failure_deficit_or_regular_obstruction {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑k∈Finset.Icc 2 (s+t),diagonal n m k) :
    ∃ F : StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧
      let D := diagonal F.n F.m (F.r+2)-1
      matchingEdges F.G+minimumExposure F.G D+1≤F.rank ∨
      ∃c:F.G.ConnectedComponent,
        envelopeReserve c.toSimpleGraph D<minimumExposure c.toSimpleGraph D ∧
        (∀x:c.supp,Nat.card (F.G.neighborSet x.val)=D) ∧
        PerfectAfterEveryDeletion c.toSimpleGraph ∧ Even D ∧ 4≤D := by
  obtain ⟨F,paid,_,_⟩ := failure_has_smaller_rank_baseline.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_deficit_or_regular_obstruction F paid⟩

#print axioms strict_source_deficit_or_regular_obstruction
#print axioms strict_source_deficit_of_resolved_components
#print axioms original_failure_deficit_or_regular_obstruction
end JSP452Audit.StarHost
