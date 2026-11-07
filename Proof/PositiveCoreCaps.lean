import RegionWeights
import RegularCriticalHost
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The handshaking bound for a genuine finite simple graph with a uniform
degree cap, expressed using the cardinalities used in the reserve formulas. -/
private theorem handshake_cap {X : Type*} [Finite X] (Q : SimpleGraph X) (k : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ k) :
    2*Q.edgeSet.ncard ≤ Nat.card X * k := by
  classical
  let _ := Fintype.ofFinite X
  have edges : Q.edgeSet.ncard = Q.edgeFinset.card := by
    rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.edgeFinset_card]
  rw [edges,← Q.sum_degrees_eq_twice_card_edges,Nat.card_eq_fintype_card]
  calc
    (∑ x, Q.degree x) ≤ ∑ _x : X, k := Finset.sum_le_sum (fun x _ => by
      simpa only [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree] using cap x)
    _ = _ := by simp

/-- A factor-critical positive-surplus core has at least D+1 vertices,
and the signed surplus is at most both half the degree cap and the rank. -/
theorem positive_core_caps {X : Type*} [Finite X] [Nonempty X] (Q : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion Q) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (positive : 0 < edgeSurplus Q D) :
    D+1 ≤ Nat.card X ∧ 2*edgeSurplus Q D ≤ (D : ℤ) ∧ edgeSurplus Q D ≤ (matchingEdges Q : ℤ) := by
  classical
  let _ := Fintype.ofFinite X
  let z := matchingEdges Q
  have order : Nat.card X = 2*z+1 := factorCritical_order_rank Q crit (Classical.arbitrary X)
  have simple (v : X) : Nat.card (Q.neighborSet v) ≤ 2*z := by
    have degree := Q.degree_lt_card_verts v
    rw [← Nat.card_eq_fintype_card,order] at degree
    rw [Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
    omega
  have W : edgeSurplus Q D = (Q.edgeSet.ncard : ℤ) - ↑(D*z) := by
    simp [edgeSurplus,z]
  have enough : D ≤ 2*z := by
    by_contra! bad
    have many := handshake_cap Q (2*z) simple
    have upper : Nat.card X * (2*z) ≤ D * (2*z) := Nat.mul_le_mul_right _ (by omega)
    have capE := many.trans upper
    rw [Nat.mul_left_comm D 2 z] at capE
    omega
  have general := handshake_cap Q D cap
  rw [order,Nat.add_mul,Nat.one_mul,Nat.mul_assoc,Nat.mul_comm z D] at general
  have boundW : 2*edgeSurplus Q D ≤ (D : ℤ) := by omega
  exact ⟨by omega,boundW,by omega⟩

#print axioms positive_core_caps
end JSP452Audit.StarHost
