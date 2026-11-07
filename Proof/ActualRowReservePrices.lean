import GlobalComponentReserve
import HighDegreeEntry
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {s t : ℕ}

/-- The exact row-price bridge uses only the reserve of this very host.
The parameter is an explicit mathematical obligation, never a new axiom. -/
theorem row_price_of_envelope_payment (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤k+1)
    (pay : minimumExposure G D≤envelopeReserve G k) :
    rowEnergy n m r + matchingEdges G + minimumExposure G D ≤ G.edgeSet.ncard + rowCount s t r := by
  have account := row_envelope_reserve hs ht n m hn hm pn pm G r k row height
  omega

theorem rich_row_of_envelope_payment (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤k+1)
    (pay : minimumExposure G D≤envelopeReserve G k)
    (rich : rowCount s t r≤matchingEdges G) :
    rowEnergy n m r+minimumExposure G D≤G.edgeSet.ncard := by
  have account := row_price_of_envelope_payment hs ht n m hn hm pn pm G r D k row height pay
  omega

theorem strict_row_of_envelope_payment (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤k+1)
    (pay : minimumExposure G D≤envelopeReserve G k)
    (strict : G.edgeSet.ncard<rowEnergy n m r) :
    matchingEdges G+minimumExposure G D+1≤rowCount s t r := by
  have account := row_price_of_envelope_payment hs ht n m hn hm pn pm G r D k row height pay
  omega

/-- Every actual strict row either has the required stronger rank deficit,
or contains an actual unpaid component of the original host. Regularity and
criticality require the extra degree assumptions in the subsequent source bridge. -/
theorem strict_row_deficit_or_unpaid_component (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D k : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤k+1)
    (strict : G.edgeSet.ncard<rowEnergy n m r) :
    matchingEdges G+minimumExposure G D+1≤rowCount s t r ∨
    ∃c:G.ConnectedComponent,envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D := by
  by_cases pay : minimumExposure G D≤envelopeReserve G k
  · exact Or.inl (strict_row_of_envelope_payment hs ht n m hn hm pn pm G r D k row height pay strict)
  · exact Or.inr (exists_unpaid_original_component G D k (Nat.lt_of_not_ge pay))

/-- The former noReg input is a checked actual-graph condition here. -/
theorem ported_strict_row_deficit (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D : ℕ)
    (pos : 0<D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (noReg : NoOriginalRegularCritical G D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (height : diagonal n m (r+2)≤D+1)
    (strict : G.edgeSet.ncard<rowEnergy n m r) :
    matchingEdges G+minimumExposure G D+1≤rowCount s t r := by
  exact strict_row_of_envelope_payment hs ht n m hn hm pn pm G r D D row height
    (ported_reserve G D D pos cap noReg).2 strict

#print axioms row_price_of_envelope_payment
#print axioms rich_row_of_envelope_payment
#print axioms strict_row_of_envelope_payment
#print axioms strict_row_deficit_or_unpaid_component
#print axioms ported_strict_row_deficit
end JSP452Audit.StarHost
