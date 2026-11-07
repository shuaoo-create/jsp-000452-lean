import ComponentBudget
namespace JSP452Audit.StarHost
open SimpleGraph

theorem delete_vertex_order {X : Type*} [Finite X] (v : X) :
    Nat.card {x : X // x≠v} + 1 = Nat.card X := by
  have outside : Nat.card {x : X // x≠v} = Nat.card X - 1 := by
    change Nat.card ↥(({v} : Set X)ᶜ) = _
    rw [Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_singleton]
  have pos : 0 < Nat.card X := @Nat.card_pos _ ⟨v⟩ _
  omega

/-- The weak upper of two on odd components is already sufficient: both
    component counts have the parity of their vertex counts, which differ by one. -/
theorem restore_odd_loss {X : Type*} [Finite X] (H : SimpleGraph X) (v : X)
    (weak : (H.induce {x | x≠v}).oddComponents.ncard ≤ H.oddComponents.ncard + 2) :
    (H.induce {x | x≠v}).oddComponents.ncard ≤ H.oddComponents.ncard + 1 := by
  have small := halfComponents_account (H.induce {x | x≠v})
  have large := halfComponents_account H
  have combined : 2*halfComponents (H.induce {x | x≠v}) + (H.induce {x | x≠v}).oddComponents.ncard + 1 =
      2*halfComponents H + H.oddComponents.ncard :=
    (congrArg (fun n : ℕ => n+1) small).trans ((delete_vertex_order v).trans large.symm)
  omega

/-- Exact integer score comparison; negative cut scores are included. -/
theorem restore_score_step {X : Type*} [Finite X] (H : SimpleGraph X) (v : X) (otherDeleted : ℕ)
    (weak : (H.induce {x | x≠v}).oddComponents.ncard ≤ H.oddComponents.ncard + 2) :
    ((H.induce {x | x≠v}).oddComponents.ncard : ℤ) - (otherDeleted+1 : ℕ) ≤
      (H.oddComponents.ncard : ℤ) - otherDeleted := by
  have := restore_odd_loss H v weak
  omega

#print axioms restore_odd_loss
#print axioms restore_score_step
end JSP452Audit.StarHost
