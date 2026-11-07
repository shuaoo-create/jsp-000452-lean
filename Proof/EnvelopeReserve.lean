import UniformEnvelope
import ReserveRowBudget
import SmallerSourcePrice
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Only positive heights above one enter the reserve. Height one is
accounted for separately by the actual matching number. -/
noncomputable def envelopeReserve {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) : ℕ :=
  G.edgeSet.ncard - (matchingEdges G + ∑ j∈Finset.range D,uniformEnvelope G (j+2))

theorem envelope_reserve_account {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) :
    envelopeReserve G D + (matchingEdges G + ∑ j∈Finset.range D,uniformEnvelope G (j+2))=G.edgeSet.ncard ∧
      baseReserve G D ≤ envelopeReserve G D := by
  have sub := Finset.sum_le_sum (s:=Finset.range D)
    (fun j _ => uniformEnvelope_le_deletion G (j+1) (by omega))
  change (∑j∈Finset.range D,uniformEnvelope G (j+2)) ≤ ∑j∈Finset.range D,deletionBudget G (j+1) at sub
  have old := base_reserve_account G D
  unfold envelopeReserve
  omega

theorem uniform_envelope_vanishes_above {X : Type*} [Finite X] (G : SimpleGraph X) (D j : ℕ)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (above : D<j) : uniformEnvelope G (j+1)=0 := by
  have endAt := deletionBudget_zero_above G j (by omega) (fun x => (cap x).trans_lt above)
  have := uniformEnvelope_le_deletion G j (by omega)
  omega

theorem row_envelope_reserve {X : Type*} [Finite X] {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X) (r D : ℕ)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (peak : diagonal n m (r+2) ≤ D+1) :
    rowEnergy n m r + matchingEdges G + envelopeReserve G D ≤ G.edgeSet.ncard + rowCount s t r := by
  have area : rowEnergy n m r = ∑ k∈Finset.range (D+1),widthAt n m r (k+1) := by
    apply finite_layer_count (fun k => diagonal n m (r+k+2))
    intro k hk
    exact (earlier_diagonal_dominates hs ht n m hn hm (show r≤r+k by omega)
      (by dsimp [rowCount] at hk; omega)).trans peak
  rw [Finset.sum_range_succ'] at area
  have first : widthAt n m r 1=rowCount s t r := first_layer_complete hs ht n m pn pm r
  simp only [Nat.zero_add,first] at area
  change rowEnergy n m r = (∑ j∈Finset.range D,widthAt n m r (j+2)) + rowCount s t r at area
  have pay := Finset.sum_le_sum (s:=Finset.range D)
    (fun j _ => widthAt_le_uniformEnvelope hs ht n m hn hm pn pm G r (j+2) row (by omega))
  have bal := (envelope_reserve_account G D).1
  omega
#print axioms envelope_reserve_account
#print axioms row_envelope_reserve
end JSP452Audit.StarHost