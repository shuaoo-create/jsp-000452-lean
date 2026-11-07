import IndependentLayers
import IndependentRegularTop
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The first removed vertex costs no matching rank in a factor-critical host.
Every subsequent removed label costs at most one. -/
theorem factorCritical_cut_rank (Q : SimpleGraph X) (crit : PerfectAfterEveryDeletion Q)
    (I : Set X) (nonempty : I.Nonempty) : matchingEdges Q+1 ≤ matchingEdges (Q.induce Iᶜ)+I.ncard := by
  obtain ⟨v,hv⟩ := nonempty
  let S : Set X := {v}
  let Z : Set ↥(Sᶜ : Set X) := {w | w.val ∈ I}
  have eq : outerCut S Z = I := by
    ext x
    constructor
    · rintro (inS|⟨z,hz,rfl⟩)
      · have same : x=v := inS
        exact same.symm ▸ hv
      · exact hz
    · intro hx
      by_cases inS : x∈S
      · exact Or.inl inS
      · exact Or.inr ⟨⟨x,inS⟩,hx,rfl⟩
  have count := outerCut_ncard S Z
  rw [eq,show S.ncard=1 from Set.ncard_singleton v] at count
  have reserve := matching_rank_le_cut_add (Q.induce Sᶜ) Z
  have rank := rank_eq_of_graph_iso (nestedCutIso Q S Z)
  rw [eq] at rank
  rw [rank] at reserve
  change matchingEdges (Q.induce {x|x≠v}) ≤ _ at reserve
  rw [factorCritical_delete_rank Q crit v] at reserve
  omega

/-- The independent-set identity of the regular factor-critical branch,
with no parity or nonnegativity lost to truncated subtractions. -/
theorem regular_independent_reserve [Nonempty X] (Q : SimpleGraph X) (d : ℕ)
    (reg : ∀x,Nat.card (Q.neighborSet x)=d+1) (crit : PerfectAfterEveryDeletion Q)
    (I : Set X) (nonempty : I.Nonempty) (indep : Q.IsIndepSet I) :
    let H := Q.induce Iᶜ
    baseReserve Q (d+1) = baseReserve H (d+1) + (I.ncard+matchingEdges H-(matchingEdges Q+1)) +
      ∑ j∈Finset.range d,savedAt Q I (j+1) := by
  intro H
  have balance := independent_layers_account Q I d indep (fun x _ => reg x)
  have first := regular_factorCritical_top_budget_one Q (d+1) (by omega) reg crit
  have next := factorCritical_top_budget_after_nonempty_cut Q (d+1) (by omega) (fun x => (reg x).le) crit I nonempty
  have nonneg := factorCritical_cut_rank Q crit I nonempty
  change matchingEdges Q+1 ≤ matchingEdges H+I.ncard at nonneg
  change baseReserve Q (d+1)+matchingEdges Q+deletionBudget Q (d+1)=
    baseReserve H (d+1)+matchingEdges H+deletionBudget H (d+1)+I.ncard+_ at balance
  change deletionBudget H (d+1)=0 at next
  rw [first,next] at balance
  omega
#print axioms factorCritical_cut_rank
#print axioms regular_independent_reserve
end JSP452Audit.StarHost