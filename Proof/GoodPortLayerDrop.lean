import MixedPortUncovered
import IndependentRegularTop
import BudgetCeiling

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- A full vertex sees every other vertex: the full side is a clique, and the
good low vertices already have all cross edges to the full side. -/
theorem good_port_full_universal (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x ∈ portLow Q D, GoodPort Q x) (clique : Q.IsClique (portFull Q D))
    (v : X) (full : v ∈ portFull Q D) : ∀ w, w ≠ v → Q.Adj v w := by
  intro w different
  by_cases hw : w ∈ portFull Q D
  · exact clique full hw different.symm
  · exact full_adj_good_low Q D cap crit good full (lt_of_le_of_ne (cap w) hw)

/-- Deleting an actual universal vertex removes exactly one neighbor of
every remaining vertex, preserving the original labels of all others. -/
theorem delete_full_neighbor_count (Q : SimpleGraph X) (v : X)
    (univ : ∀ w, w ≠ v → Q.Adj v w) (x : {w : X // w ≠ v}) :
    Nat.card ((Q.induce {w | w ≠ v}).neighborSet x) + 1 = Nat.card (Q.neighborSet x.val) := by
  let eq : ((Q.induce {w | w ≠ v}).neighborSet x) ≃ ↥(Q.neighborSet x.val \ {v}) := {
    toFun := fun z => ⟨z.val.val,z.property,fun h => z.val.property (Set.mem_singleton_iff.mp h)⟩
    invFun := fun w => ⟨⟨w.val,fun h => w.property.2 (Set.mem_singleton_iff.mpr h)⟩,w.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have adjacent : v ∈ Q.neighborSet x.val := (univ x.val x.property).symm
  have split := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr adjacent)
  rw [Set.ncard_singleton] at split
  rw [Nat.card_congr eq,Nat.card_coe_set_eq]
  exact split

theorem good_port_layer_drop (Q : SimpleGraph X) (D : ℕ) (hD : 2 ≤ D)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x ∈ portLow Q D, GoodPort Q x) (clique : Q.IsClique (portFull Q D))
    (v : X) (full : v ∈ portFull Q D) :
    let H := Q.induce {w | w ≠ v}
    (∀ x, Nat.card (H.neighborSet x) ≤ D-1) ∧ deletionBudget H (D-1) = 0 := by
  intro H
  have universal := good_port_full_universal Q D cap crit good clique v full
  have newCap (x : {w : X // w ≠ v}) : Nat.card (H.neighborSet x) ≤ D-1 := by
    have exactDegree := delete_full_neighbor_count Q v universal x
    have bound := cap x.val
    change Nat.card (H.neighborSet x) + 1 = Nat.card (Q.neighborSet x.val) at exactDegree
    omega
  exact ⟨newCap,top_budget_zero_of_perfect H (D-1) (by omega) newCap (crit v)⟩

/-- For any odd-order graph whose order is at most the even positive cap D,
every degree is below D-1. In particular this applies to an isolated odd clique. -/
theorem odd_order_layer_zero (Q : SimpleGraph X) (D : ℕ) (hD : 2 ≤ D)
    (evenD : Even D) (oddOrder : Odd (Nat.card X)) (order : Nat.card X ≤ D) :
    deletionBudget Q (D-1) = 0 := by
  classical
  let _ := Fintype.ofFinite X
  apply deletionBudget_zero_above Q (D-1) (by omega)
  intro x
  have bound := Q.degree_lt_card_verts x
  rw [← Nat.card_eq_fintype_card (α := X)] at bound
  have actual : Nat.card (Q.neighborSet x) = Q.degree x := by
    rw [Nat.card_eq_fintype_card,card_neighborSet_eq_degree]
  obtain ⟨a,ha⟩ := evenD
  obtain ⟨b,hb⟩ := oddOrder
  omega

#print axioms good_port_full_universal
#print axioms delete_full_neighbor_count
#print axioms good_port_layer_drop
#print axioms odd_order_layer_zero
end JSP452Audit.StarHost
