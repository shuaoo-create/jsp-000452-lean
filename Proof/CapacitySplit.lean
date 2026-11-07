import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Powerset

namespace JSP452Audit.StarHost

/-- An actual bipartition of a finite menu fits the two capacities when their
excess above the total is r and no indivisible item has weight above r+1. -/
theorem capacity_split {I : Type*} [Fintype I] [DecidableEq I] (z : I → ℕ) (i j r : ℕ)
    (total : i+j = r + ∑ k, z k) (small : ∀ k, z k ≤ r+1) :
    ∃ F : Finset I, (∑ k ∈ F, z k) ≤ i ∧ (∑ k ∈ Fᶜ, z k) ≤ j ∧
      (∑ k ∈ F, z k) + (∑ k ∈ Fᶜ, z k) = ∑ k, z k := by
  classical
  let weight (F : Finset I) := ∑ k ∈ F, z k
  let possible := (Finset.univ : Finset (Finset I)).filter (fun F => weight F ≤ i)
  have empty : ∅ ∈ possible := Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [weight]⟩
  obtain ⟨F,yes,best⟩ := Finset.exists_max_image possible weight ⟨∅,empty⟩
  have fit : weight F ≤ i := (Finset.mem_filter.mp yes).2
  have add : weight F + weight Fᶜ = ∑ k, z k := Finset.sum_add_sum_compl F z
  refine ⟨F,fit,?_,add⟩
  change weight Fᶜ ≤ j
  by_cases more : ∃ k, k ∉ F ∧ 0 < z k
  · obtain ⟨k,absent,pos⟩ := more
    have newCost : weight (insert k F) = z k + weight F := Finset.sum_insert absent
    have over : i < weight (insert k F) := by
      by_contra! no
      have member : insert k F ∈ possible := Finset.mem_filter.mpr ⟨Finset.mem_univ _,no⟩
      have le := best (insert k F) member
      omega
    have bound := small k
    omega
  · have none : weight Fᶜ = 0 := Finset.sum_eq_zero (fun k hk => by
      have notPos : ¬ 0 < z k := fun pos => more ⟨k,Finset.mem_compl.mp hk,pos⟩
      omega)
    omega

#print axioms capacity_split
end JSP452Audit.StarHost
