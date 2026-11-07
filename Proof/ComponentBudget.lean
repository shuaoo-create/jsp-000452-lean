import Mathlib.Combinatorics.SimpleGraph.Tutte

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The sum of the integer half-orders of the actual connected components. -/
noncomputable def halfComponents {X : Type*} [Finite X] (G : SimpleGraph X) : ℕ := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  exact ∑ c : G.ConnectedComponent, c.supp.ncard / 2

theorem halfComponents_account {X : Type*} [Finite X] (G : SimpleGraph X) :
    2 * halfComponents G + G.oddComponents.ncard = Nat.card X := by
  classical
  let _ := Fintype.ofFinite G.ConnectedComponent
  have total : (∑ c : G.ConnectedComponent, c.supp.ncard) = Nat.card X := by
    simp_rw [← Nat.card_coe_set_eq]
    rw [← Nat.card_sigma]
    exact Nat.card_congr (Equiv.sigmaFiberEquiv G.connectedComponentMk)
  have oddSum : G.oddComponents.ncard =
      ∑ c : G.ConnectedComponent, (if Odd c.supp.ncard then 1 else 0) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, Finset.sum_boole]
    exact Fintype.card_subtype (fun c : G.ConnectedComponent => Odd c.supp.ncard)
  rw [← total,oddSum]
  unfold halfComponents
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  split_ifs with odd
  · have := Nat.odd_iff.mp odd
    omega
  · have := mt Nat.odd_iff.mpr odd
    omega

/-- Cardinality of odd components is invariant under a genuine graph isomorphism. -/
theorem odd_ncard_iso {X Y : Type*} {G : SimpleGraph X} {H : SimpleGraph Y}
    (e : G ≃g H) : G.oddComponents.ncard = H.oddComponents.ncard := by
  have eq (c : G.ConnectedComponent) : c.supp.ncard = (e.connectedComponentEquiv c).supp.ncard :=
    Nat.card_congr (SimpleGraph.ConnectedComponent.isoEquivSupp e c)
  exact Nat.card_congr (Equiv.subtypeEquiv e.connectedComponentEquiv fun c => by
    change Odd c.supp.ncard ↔ Odd (e.connectedComponentEquiv c).supp.ncard
    rw [eq])

#print axioms halfComponents_account
#print axioms odd_ncard_iso
end JSP452Audit.StarHost
