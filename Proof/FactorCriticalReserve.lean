import FactorCriticalPeak
import StrictReserveStep
import StrictSourcePays
import TopColumnExposure
namespace JSP452Audit.StarHost
open SimpleGraph
/-- A finite graph that stays perfectly matchable after deletion of any
vertex, but has both a full and a lower-degree vertex, has strict reserve. -/
theorem factorCritical_nonregular_reserve {X : Type*} [Finite X] (G : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion G) (D H : ℕ) (peak : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (v y : X) (full : Nat.card (G.neighborSet v)=D) (low : Nat.card (G.neighborSet y)<D) :
    baseReserve (G.induce {x|x≠v}) H + 1 ≤ baseReserve G H := by
  have pos : 0<D := by omega
  exact strict_reserve_delete_peak G v D H pos full peak
    (factorCritical_peak_budget_zero G D pos peak crit y low) (factorCritical_delete_rank G crit v)

/-- A complete suffix row at the limiting degree, if factor-critical, has
no below-maximum-degree vertices at all. -/
theorem factorCritical_forcing_row_regular {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (bound : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1)
    (crit : PerfectAfterEveryDeletion G) :
    ∀ x, Nat.card (G.neighborSet x)=diagonal n m (r+2)-1 := by
  have ⟨nonzero,col⟩ := row_minimum_exposure hs ht n m hn hm pn pm G r live row bound
  intro y
  by_contra neq
  have zero := factorCritical_peak_exposure_zero G (diagonal n m (r+2)-1) crit y
    (lt_of_le_of_ne (bound y) neq)
  omega
#print axioms factorCritical_nonregular_reserve
#print axioms factorCritical_forcing_row_regular
end JSP452Audit.StarHost