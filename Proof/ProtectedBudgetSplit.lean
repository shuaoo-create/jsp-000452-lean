import ComponentZeroReserve

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

/-- Deletion costs add for a partition of an actual labeled induced graph with no crossing edge. -/
theorem deletionBudget_split_regions {X : Type*} [Finite X] (G : SimpleGraph X)
    (K P Q : Set X) (j : ℕ) (cover : P∪Q=K) (apart : Disjoint P Q)
    (sep : ∀ x∈P, ∀ y∈Q, ¬G.Adj x y) :
    deletionBudget (G.induce K) j = deletionBudget (G.induce P) j + deletionBudget (G.induce Q) j := by
  rw [← deletionBudget_iso (regionSumIso G K P Q cover apart sep) j,deletionBudget_sumGraph]

/-- A separated set and its complement have exactly additive deletion budgets at every layer. -/
theorem deletionBudget_split_cut {X : Type*} [Finite X] (K : SimpleGraph X) (C : Set X) (j : ℕ)
    (sep : ∀ x∈C, ∀ y∈Cᶜ, ¬K.Adj x y) :
    deletionBudget K j = deletionBudget (K.induce C) j + deletionBudget (K.induce Cᶜ) j := by
  rw [← deletionBudget_iso (induceUnivIso K) j]
  exact deletionBudget_split_regions K Set.univ C Cᶜ j (Set.union_compl_self C) disjoint_compl_right sep

#print axioms deletionBudget_mono_embedding
#print axioms deletionBudget_split_regions
#print axioms deletionBudget_split_cut
end JSP452Audit.StarHost
