import TutteBergeExact

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
variable {X : Type*} [Finite X]

/-- A real Tutte--Berge cut attaining the global unmatched-vertex deficit. -/
def IsTightBarrier (G : SimpleGraph X) (S : Set X) : Prop :=
  (G.induce Sᶜ).oddComponents.ncard = S.ncard + minUnmatched G

theorem exists_largest_tight_barrier (G : SimpleGraph X) :
    ∃ S : Set X, IsTightBarrier G S ∧ ∀ A : Set X, IsTightBarrier G A → A.ncard ≤ S.ncard := by
  let sizes : Set ℕ := {n | ∃ A : Set X, IsTightBarrier G A ∧ A.ncard = n}
  have bounded : BddAbove sizes := by
    refine ⟨Nat.card X,?_⟩
    rintro k ⟨A,_,rfl⟩
    simpa only [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ A)
  obtain ⟨A,tight⟩ := tutte_berge_attained G
  have nonempty : sizes.Nonempty := ⟨_,A,tight,rfl⟩
  obtain ⟨S,hS,largest⟩ := Nat.sSup_mem nonempty bounded
  refine ⟨S,hS,fun B hB => ?_⟩
  exact (le_csSup bounded (show B.ncard ∈ sizes from ⟨B,hB,rfl⟩)).trans_eq largest.symm

/-- No proper superset of a largest tight cut attains the bound. -/
theorem strict_of_strict_superset_largest_tight (G : SimpleGraph X) (S U : Set X)
    (maximal : ∀ A : Set X, IsTightBarrier G A → A.ncard ≤ S.ncard) (hSU : S ⊂ U) :
    (G.induce Uᶜ).oddComponents.ncard < U.ncard + minUnmatched G := by
  have upper := tutte_berge_upper_all G U
  refine lt_of_le_of_ne upper ?_
  intro eq
  exact (Set.ncard_lt_ncard hSU).not_ge (maximal U eq)

theorem exists_tight_barrier_with_strict_supersets (G : SimpleGraph X) :
    ∃ S : Set X, IsTightBarrier G S ∧
      (∀ A : Set X, IsTightBarrier G A → A.ncard ≤ S.ncard) ∧
      ∀ U : Set X, S ⊂ U → (G.induce Uᶜ).oddComponents.ncard < U.ncard + minUnmatched G := by
  obtain ⟨S,hs,hm⟩ := exists_largest_tight_barrier G
  exact ⟨S,hs,hm,fun U h => strict_of_strict_superset_largest_tight G S U hm h⟩

#print axioms exists_largest_tight_barrier
#print axioms strict_of_strict_superset_largest_tight
#print axioms exists_tight_barrier_with_strict_supersets
end JSP452Audit.StarHost
