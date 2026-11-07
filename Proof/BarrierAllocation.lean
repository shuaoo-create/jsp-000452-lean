import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Set.Card

namespace JSP452Audit.StarHost

/- Allocate each cost in a finite subfamily. The split is defined on the entire
index type, so induction can extend it without changing any previous value. -/
private theorem split_sum_on {C : Type*} (I : Finset C) (cost : C → ℕ)
    (p q : ℕ) (afford : ∑ c ∈ I, cost c ≤ p + q) :
    ∃ red blue : C → ℕ, (∀ c, red c + blue c = cost c) ∧
      (∑ c ∈ I, red c) ≤ p ∧ (∑ c ∈ I, blue c) ≤ q := by
  classical
  induction I using Finset.induction_on generalizing p q with
  | empty => exact ⟨fun _ => 0, cost, by simp, by simp, by simp⟩
  | @insert a I ha ih =>
    rw [Finset.sum_insert ha] at afford
    let x := min (cost a) p
    let y := cost a - x
    have xle : x ≤ p := Nat.min_le_right _ _
    have balance : x + y = cost a := by dsimp [x,y]; omega
    have yle : y ≤ q := by dsimp [x,y]; omega
    have rest : (∑ c ∈ I, cost c) ≤ (p - x) + (q - y) := by omega
    obtain ⟨r,b,parts,hr,hb⟩ := ih (p - x) (q - y) rest
    let R := Function.update r a x
    let B := Function.update b a y
    have unchanged (c : C) (hc : c ∈ I) : c ≠ a := fun eq => ha (eq ▸ hc)
    have rsum : (∑ c ∈ I, R c) = ∑ c ∈ I, r c :=
      Finset.sum_congr rfl fun c hc => Function.update_of_ne (unchanged c hc) _ _
    have bsum : (∑ c ∈ I, B c) = ∑ c ∈ I, b c :=
      Finset.sum_congr rfl fun c hc => Function.update_of_ne (unchanged c hc) _ _
    refine ⟨R,B,?_,?_,?_⟩
    · intro c
      by_cases e : c = a
      · subst c; simpa [R,B] using balance
      · simpa [R,B,Function.update_of_ne e] using parts c
    · rw [Finset.sum_insert ha, rsum]
      have eq : R a = x := Function.update_self ..
      omega
    · rw [Finset.sum_insert ha, bsum]
      have eq : B a = y := Function.update_self ..
      omega

/-- Split both the barrier and each component exactly, staying within both color budgets. -/
theorem barrier_allocation {C : Type*} [Fintype C] (cost : C → ℕ) (b p q : ℕ)
    (total : b + (∑ c, cost c) ≤ p + q) :
    ∃ br bb : ℕ, ∃ red blue : C → ℕ,
      br + bb = b ∧ (∀ c, red c + blue c = cost c) ∧
      br + (∑ c, red c) ≤ p ∧ bb + (∑ c, blue c) ≤ q := by
  let br := min b p
  let bb := b - br
  have brle : br ≤ p := Nat.min_le_right _ _
  have bble : bb ≤ q := by dsimp [br,bb]; omega
  have parts : br + bb = b := by dsimp [br,bb]; omega
  have costle : (∑ c, cost c) ≤ (p - br) + (q - bb) := by omega
  obtain ⟨red,blue,splits,hr,hb⟩ := split_sum_on Finset.univ cost _ _ costle
  exact ⟨br,bb,red,blue,parts,splits,by omega,by omega⟩

/-- Realize the barrier allocation by a subset of the prescribed cardinality. -/
theorem exists_set_ncard_of_le {T : Type*} [Finite T] (k : ℕ) (hk : k ≤ Nat.card T) :
    ∃ A : Set T, A.ncard = k := by
  obtain ⟨A, _, hA⟩ := Set.exists_subset_card_eq (s := (Set.univ : Set T)) (by simpa using hk)
  exact ⟨A,hA⟩

#print axioms barrier_allocation
#print axioms exists_set_ncard_of_le
end JSP452Audit.StarHost
