import TheSameMaximumMatchingOnThePieceAndItsExterior
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
universe u

theorem containing_barrier_residual_strict {X:Type u} [Finite X] (G:SimpleGraph X) (S:Set X)
    (tight:IsTightBarrier G S) (maximal:∀A:Set X,S⊆A → IsTightBarrier G A → A.ncard≤S.ncard)
    (Z:Set ↥(Sᶜ:Set X)) (present:Z.Nonempty) :
    ((G.induce Sᶜ).induce Zᶜ).oddComponents.ncard<(G.induce Sᶜ).oddComponents.ncard+Z.ncard := by
  have upper := tutte_berge_upper_all G (outerCut S Z)
  have ext := outerCut_strict S Z present
  have less : (G.induce (outerCut S Z)ᶜ).oddComponents.ncard<(outerCut S Z).ncard+minUnmatched G := by
    apply lt_of_le_of_ne upper
    intro equal
    exact (Set.ncard_lt_ncard ext).not_ge (maximal _ ext.1 equal)
  have iso := odd_ncard_iso (nestedCutIso G S Z)
  rw [outerCut_ncard] at less
  change (G.induce Sᶜ).oddComponents.ncard=S.ncard+minUnmatched G at tight
  omega

theorem containing_barrier_components {X : Type*} [Finite X] (G : SimpleGraph X)
    (S : Set X) (tight : IsTightBarrier G S)
    (maximal : ∀ A : Set X, S⊆A → IsTightBarrier G A → A.ncard≤S.ncard)
    (c : (G.induce Sᶜ).ConnectedComponent) :
    Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion ((G.induce Sᶜ).induce c.supp) := by
  classical
  let Y := G.induce Sᶜ
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  apply odd_critical_of_strict_nonempty_cuts
  intro Z hz
  let U : Set ↥(Sᶜ : Set X) := Subtype.val '' Z
  have nonempty : U.Nonempty := hz.image _
  have ncard : U.ncard=Z.ncard := Set.ncard_image_of_injective _ Subtype.val_injective
  have strict := containing_barrier_residual_strict G S tight maximal U nonempty
  have replace := odd_components_replace_component Y c Z
  change (Y.induce Uᶜ).oddComponents.ncard < Y.oddComponents.ncard + U.ncard at strict
  change (Y.induce Uᶜ).oddComponents.ncard + _ = Y.oddComponents.ncard + _ at replace
  change ((Y.induce c.supp).induce Zᶜ).oddComponents.ncard < (if Odd (Nat.card c.supp) then 1 else 0) + Z.ncard
  omega


theorem extend_tight_barrier_to_critical {X:Type u} [Finite X] (G:SimpleGraph X) (U:Set X)
    (initial:IsTightBarrier G U) : ∃S:Set X,U⊆S ∧ IsTightBarrier G S ∧
    ∀c:(G.induce Sᶜ).ConnectedComponent,Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph := by
  let sizes : Set ℕ := {n | ∃S:Set X,U⊆S ∧ IsTightBarrier G S ∧ S.ncard=n}
  have bounded : BddAbove sizes := by
    refine ⟨Nat.card X,?_⟩
    rintro _ ⟨S,_,_,rfl⟩
    simpa only [Set.ncard_univ] using Set.ncard_le_ncard (Set.subset_univ S)
  have nonempty : sizes.Nonempty := ⟨U.ncard,U,Set.Subset.rfl,initial,rfl⟩
  obtain ⟨S,contains,tight,size⟩ := Nat.sSup_mem nonempty bounded
  have maximal (A:Set X) (inc:S⊆A) (t:IsTightBarrier G A) : A.ncard≤S.ncard :=
    (le_csSup bounded (show A.ncard∈sizes from ⟨A,contains.trans inc,t,rfl⟩)).trans_eq size.symm
  exact ⟨S,contains,tight,containing_barrier_components G S tight maximal⟩

theorem critical_barrier_after_prescribed_rank_loss {X:Type u} [Finite X] (G:SimpleGraph X) (A:Set X)
    (rank:matchingEdges G=A.ncard+matchingEdges (G.induce Aᶜ)) :
    ∃S:Set X,A⊆S ∧ IsTightBarrier G S ∧ ∀c:(G.induce Sᶜ).ConnectedComponent,
      Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph := by
  obtain ⟨B,tightB⟩ := tutte_berge_attained (G.induce Aᶜ)
  have nG := minUnmatched_add_twice_matching G
  have nA := minUnmatched_add_twice_matching (G.induce Aᶜ)
  rw [Nat.card_coe_set_eq] at nA
  have count := Set.ncard_add_ncard_compl A
  have unmatched : minUnmatched (G.induce Aᶜ)=minUnmatched G+A.ncard := by omega
  have joined : IsTightBarrier G (outerCut A B) := by
    change (G.induce (outerCut A B)ᶜ).oddComponents.ncard=(outerCut A B).ncard+minUnmatched G
    rw [←odd_ncard_iso (nestedCutIso G A B),tightB,outerCut_ncard,unmatched];omega
  obtain ⟨S,inc,tight,crit⟩ := extend_tight_barrier_to_critical G _ joined
  exact ⟨S,Set.subset_union_left.trans inc,tight,crit⟩
#print axioms containing_barrier_components
#print axioms extend_tight_barrier_to_critical
#print axioms critical_barrier_after_prescribed_rank_loss
end JSP452Audit.StarHost
