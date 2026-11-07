import ReserveRowBudget
namespace JSP452Audit.StarHost
open SimpleGraph
/-- On an actual strict source the matching-rank gap must pay for every
certified unit of the base reserve in addition to the missing edge. -/
theorem strict_source_pays_reserve {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (strict : G.edgeSet.ncard < rowEnergy n m r) :
    matchingEdges G + baseReserve G (n ⟨0,hs⟩+m ⟨0,ht⟩-2) + 1 ≤ rowCount s t r := by
  have bound := reserve_row_budget hs ht n m hn hm pn pm G r row
  omega
#print axioms strict_source_pays_reserve
end JSP452Audit.StarHost