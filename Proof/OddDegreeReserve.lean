import OddRepairGeometry
import SimultaneousCutRepair
import RepairCutCosts
import IndependentExchangePays

namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type u} [Finite X]

theorem repaired_inputs_pay (G : SimpleGraph X) (D : ℕ) (pos : 0<D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) {J : Type u} [Finite J] (p : OddRepairInputs G D J) :
    ∃ I : Set X, G.IsIndepSet I ∧ (∀x∈I,Nat.card (G.neighborSet x)=D) ∧
      deletionBudget (G.induce Iᶜ) D=0 ∧
      baseReserve (G.induce Iᶜ) D + minimumExposure G D ≤ baseReserve G D := by
  obtain ⟨N,hn,support⟩ := simultaneous_cut_repair G p.M p.matching p.I p.a p.y p.b p.z
    p.disjoint p.oldAB p.oldYZ p.newAY p.b_mem p.z_mem p.a_out p.y_out p.used
  have cost := ncard_le_twice_of_subset_two_ranges _ p.b p.z p.used
  obtain ⟨rank,top⟩ := repair_cut_costs G D pos cap p.M p.matching p.maximum p.I p.exposed
    N hn (fun x => (support x).mpr) (Nat.card J) cost
  exact ⟨p.I,p.independent,p.full,top,independent_exchange_pays G D pos p.I p.independent p.full
    (Nat.card J) p.size p.enough rank top⟩

/-- For odd degree caps the independent cut has an actual repaired
matching, zero top deletion cost, and pays the full optimal exposure. -/
theorem odd_degree_independent_cut (G : SimpleGraph X) (D : ℕ) (odd : Odd D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) :
    ∃ I : Set X, G.IsIndepSet I ∧ (∀x∈I,Nat.card (G.neighborSet x)=D) ∧
      deletionBudget (G.induce Iᶜ) D=0 ∧
      baseReserve (G.induce Iᶜ) D + minimumExposure G D ≤ baseReserve G D := by
  obtain ⟨J,finite,⟨p⟩⟩ := exists_odd_repair_inputs G D odd cap
  let _ : Finite J := finite
  have parity := Nat.odd_iff.mp odd
  have pos : 0<D := by omega
  exact repaired_inputs_pay G D pos cap p

theorem odd_degree_reserve (G : SimpleGraph X) (D k : ℕ) (odd : Odd D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) :
    minimumExposure G D ≤ baseReserve G k ∧ minimumExposure G D ≤ envelopeReserve G k := by
  obtain ⟨I,_,_,_,gain⟩ := odd_degree_independent_cut G D odd cap
  have all := baseReserve_le_truncation G D k cap
  have envelope := (envelope_reserve_account G k).2
  omega

#print axioms odd_degree_independent_cut
#print axioms odd_degree_reserve
end JSP452Audit.StarHost
