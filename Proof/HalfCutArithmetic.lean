import CutObstruction
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The cardinal form needed from *one direction* of Tutte–Berge; unpacking
    a violated cut gives a budget below k using ordinary integer arithmetic. -/
theorem half_budget_of_odd_cut {X : Type*} [Finite X] (G : SimpleGraph X)
    (k : ℕ) (S : Set X) (enough : 2*k ≤ Nat.card X)
    (oddCut : S.ncard+(Nat.card X-2*k) < (G.induce Sᶜ).oddComponents.ncard) :
    S.ncard + halfComponents (G.induce Sᶜ) < k := by
  have per := halfComponents_account (G.induce Sᶜ)
  have remaining : Nat.card ↥(Sᶜ : Set X) = Nat.card X - S.ncard := by
    rw [Nat.card_coe_set_eq,Set.ncard_compl]
  rw [remaining] at per
  have size : S.ncard ≤ Nat.card X := by
    simpa [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ S)
  omega

/-- A small total vertex set itself gives a barrier certificate. -/
theorem empty_barrier_small_order {X : Type*} [Finite X] (G : SimpleGraph X)
    (k : ℕ) (small : Nat.card X < 2*k) :
    (∅ : Set X).ncard + halfComponents (G.induce (∅ : Set X)ᶜ) < k := by
  have per := halfComponents_account (G.induce (∅ : Set X)ᶜ)
  have size : Nat.card ↥((∅ : Set X)ᶜ) = Nat.card X := by
    rw [Nat.card_coe_set_eq,Set.ncard_compl]; simp
  rw [size] at per
  rw [Set.ncard_empty,Nat.zero_add]
  omega

#print axioms half_budget_of_odd_cut
end JSP452Audit.StarHost
