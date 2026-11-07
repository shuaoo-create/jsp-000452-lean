import GreedyIndependent
import PositiveSelection
import HallRegions
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Components of size at least 2Z+1 each supply original distinct full-degree
vertices outside all the selected components. -/
theorem outside_independent_supply (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (D p Z b : ℕ)
    (hD : D+1 ≤ 2*(p+1)) (many : T.ncard=p+1)
    (order : ∀ c∈T, 2*Z+1≤Nat.card c.supp) (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (sizes : b≤Z+1) :
    ∃ U : Set X, U⊆regionCore G S T ∧ G.IsIndepSet U ∧ U.ncard=b := by
  classical
  let _ := Fintype.ofFinite ↥T
  have base : (p+1)*(2*Z+1) ≤ (regionCore G S T).ncard := by
    rw [core_order_sum]
    have le := Finset.sum_le_sum (s:=(Finset.univ : Finset ↥T)) (f:=fun _ => 2*Z+1)
      (g:=fun i => Nat.card i.val.supp) (fun i _ => order i.val i.property)
    have c : Fintype.card ↥T = p+1 := (Nat.card_eq_fintype_card (α:=↥T)).symm.trans many
    simpa [c] using le
  have mult := Nat.mul_le_mul_right Z hD
  have sufficient : (D+1)*Z < (regionCore G S T).ncard := by
    rw [Nat.mul_add,Nat.mul_one,←Nat.mul_assoc,Nat.mul_comm (p+1) 2] at base
    omega
  exact greedy_independent_exact G D Z b _ cap sufficient sizes

omit [Finite X] in
theorem disjoint_regionCore_indices (G : SimpleGraph X) (S : Set X)
    {T P : Set (G.induce Sᶜ).ConnectedComponent} (dis : Disjoint T P) :
    Disjoint (regionCore G S T) (regionCore G S P) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨z,rfl,hz⟩ ⟨w,eq,hw⟩
  have same : w=z := Subtype.ext eq
  exact (Set.disjoint_left.mp dis) hz (same ▸ hw)
#print axioms outside_independent_supply
end JSP452Audit.StarHost