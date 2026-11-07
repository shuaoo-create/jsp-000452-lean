import PositiveCoreCaps
import ComponentSurplusSum
import Mathlib.Algebra.BigOperators.Ring.Finset

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- Filter on the signed surplus of the actual original component graph. -/
def positivePieces (G : SimpleGraph X) (S : Set X) (T : Set (G.induce Sᶜ).ConnectedComponent)
    (D : ℕ) : Set (G.induce Sᶜ).ConnectedComponent :=
  {c | c ∈ T ∧ 0 < edgeSurplus ((G.induce Sᶜ).induce c.supp) D}

/-- The original component correspondence preserves the number of vertices,
so the order of a union is the sum of all its component orders. -/
theorem core_order_sum (G : SimpleGraph X) (S : Set X)
    (T : Set (G.induce Sᶜ).ConnectedComponent) [Fintype T] :
    (regionCore G S T).ncard = ∑ c : T, Nat.card c.val.supp := by
  classical
  let H := G.induce (regionCore G S T)
  let _ := Fintype.ofFinite H.ConnectedComponent
  calc
    (regionCore G S T).ncard = Nat.card (Σ c : H.ConnectedComponent, c.supp) :=
      (Nat.card_congr (Equiv.sigmaFiberEquiv H.connectedComponentMk)).symm
    _ = ∑ c : H.ConnectedComponent, Nat.card c.supp := Nat.card_sigma
    _ = ∑ c : T, Nat.card c.val.supp :=
      Fintype.sum_equiv (coreComponentEquiv G S T) _ _ (coreComponent_order G S T)

/-- The signed surplus and matching rank are taken on the same induced union.
For an empty positive set every quantity in the conclusion is zero. -/
theorem positive_selection_caps (G : SimpleGraph X) (S : Set X) (tight : IsTightBarrier G S)
    (T : Set (G.induce Sᶜ).ConnectedComponent) (D : ℕ)
    (odd : ∀ c ∈ T, Odd (Nat.card c.supp))
    (crit : ∀ c ∈ T, PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp))
    (cap : ∀ c ∈ T, ∀ x, Nat.card (((G.induce Sᶜ).induce c.supp).neighborSet x) ≤ D) :
    let P := positivePieces G S T D
    let Q := G.induce (regionCore G S P)
    let W := edgeSurplus Q D
    let Z : ℤ := matchingEdges Q
    2*W ≤ (D : ℤ)*P.ncard ∧ (D : ℤ)*P.ncard ≤ 2*Z ∧ W ≤ Z := by
  classical
  intro P Q W Z
  let _ := Fintype.ofFinite ↥P
  let piece (c : P) := (G.induce Sᶜ).induce c.val.supp
  have eachPiece (c : P) : D+1 ≤ Nat.card c.val.supp ∧
      2*edgeSurplus (piece c) D ≤ (D : ℤ) ∧ edgeSurplus (piece c) D ≤ (matchingEdges (piece c) : ℤ) := by
    let _ : Nonempty c.val.supp := c.val.nonempty_supp.to_subtype
    exact positive_core_caps (piece c) (crit _ c.property.1) D (cap _ c.property.1) c.property.2
  have count : Fintype.card ↥P = P.ncard := (Nat.card_eq_fintype_card (α := ↥P)).symm
  have sum := core_surplus_eq_sum G S P D
  have first : 2*W ≤ (D : ℤ)*P.ncard := by
    change 2*edgeSurplus Q D ≤ _
    rw [show edgeSurplus Q D = ∑ c : P, edgeSurplus (piece c) D from sum,Finset.mul_sum]
    calc
      _ ≤ ∑ _c : P, (D : ℤ) := Finset.sum_le_sum (fun c _ => (eachPiece c).2.1)
      _ = _ := by simp [count,mul_comm]
  have order := core_order_sum G S P
  have rank := core_order_matching G S tight P (fun c h => odd c h.1)
  have big : (D+1)*P.ncard ≤ (regionCore G S P).ncard := by
    rw [order]
    calc
      _ = ∑ _c : P, (D+1) := by simp [count,Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum (fun c _ => (eachPiece c).1)
  rw [Nat.add_mul,Nat.one_mul,rank] at big
  have secondNat : D * P.ncard ≤ 2 * matchingEdges Q := by
    change D*P.ncard + P.ncard ≤ 2*matchingEdges Q + P.ncard at big
    omega
  have second : (D : ℤ)*P.ncard ≤ 2*Z := by dsimp only [Z]; exact_mod_cast secondNat
  exact ⟨first,second,by omega⟩

#print axioms core_order_sum
#print axioms positive_selection_caps
end JSP452Audit.StarHost
