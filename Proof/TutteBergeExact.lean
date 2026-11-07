import MatchDualJoin
namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded

private def extendedCut {X : Type*} (S : Set X) (d : ℕ) : Set (X ⊕ Fin d) :=
  {z | match z with | .inl x => x∈S | .inr _ => True}

private def splitCut {X : Type*} (S : Set X) (d : ℕ) : extendedCut S d ≃ (↥S ⊕ Fin d) where
  toFun
    | ⟨.inl x,h⟩ => .inl ⟨x,h⟩
    | ⟨.inr i,_⟩ => .inr i
  invFun
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr i => ⟨.inr i,trivial⟩
  left_inv := by rintro ⟨x | j,h⟩ <;> rfl
  right_inv := by rintro (⟨x,h⟩ | j) <;> rfl

private def residualIso {X : Type*} (G : SimpleGraph X) (S : Set X) (d : ℕ) :
    G.induce Sᶜ ≃g (tutteJoin G d).induce (extendedCut S d)ᶜ where
  toFun x := ⟨.inl x.val,x.property⟩
  invFun
    | ⟨.inl x,h⟩ => ⟨x,h⟩
    | ⟨.inr i,h⟩ => False.elim (h trivial)
  left_inv _ := rfl
  right_inv := by rintro ⟨x | j,h⟩; exacts [rfl,False.elim (h trivial)]
  map_rel_iff' := Iff.rfl

/-- Every cut's odd-component surplus is bounded by the minimum number
    of uncovered original vertices. Negative surplus retains its integer meaning. -/
theorem tutte_berge_upper_all {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X) :
    (G.induce Sᶜ).oddComponents.ncard ≤ S.ncard + minUnmatched G := by
  classical
  let _ := Fintype.ofFinite X
  let d := minUnmatched G
  have h := (tutteJoin G d).tutte.mp (join_perfect_at_deficit G) (extendedCut S d)
  rw [tutte_violator_induce] at h
  have bound := Nat.le_of_not_gt h
  have sz : (extendedCut S d).ncard = S.ncard + d := by
    have eq := Nat.card_congr (splitCut S d)
    rwa [Nat.card_sum,Nat.card_fin] at eq
  rw [← odd_ncard_iso (residualIso G S d),sz] at bound
  exact bound

/-- Exact finite Tutte–Berge identity in attained form. -/
theorem tutte_berge_attained {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ S : Set X, (G.induce Sᶜ).oddComponents.ncard = S.ncard + minUnmatched G := by
  obtain ⟨S,pay⟩ := barrier_at_matching_number G
  refine ⟨S,le_antisymm (tutte_berge_upper_all G S) ?_⟩
  have cnt := halfComponents_account (G.induce Sᶜ)
  have survive : Nat.card ↥(Sᶜ : Set X) = Nat.card X-S.ncard := by
    rw [Nat.card_coe_set_eq,Set.ncard_compl]
  rw [survive] at cnt
  have leN : S.ncard ≤ Nat.card X := by simpa using Set.ncard_le_ncard (Set.subset_univ S)
  have hM := exists_maximum_matching G
  obtain ⟨M,hM,sz⟩ := hM
  have vertexBound := Set.ncard_le_ncard (Set.subset_univ M.verts)
  rw [Set.ncard_univ,matching_vertices_eq_twice_edges hM,sz] at vertexBound
  rw [minUnmatched_eq_deficit]
  omega

/-- The auxiliary retained-score normal form now computes the matching gap:
    its maximum equals the total original host order plus the minimum unmatched. -/
theorem max_retainedScore_exact {X : Type*} [Fintype X] (G : SimpleGraph X) :
    (∀ W : Finset X, retainedScore G W ≤ Nat.card X + minUnmatched G) ∧
      ∃ W : Finset X, retainedScore G W = Nat.card X + minUnmatched G := by
  classical
  have spec (W : Set X) :
      (G.induce W).oddComponents.ncard + W.ncard ≤ Nat.card X + minUnmatched G := by
    have bd := tutte_berge_upper_all G Wᶜ
    rw [compl_compl] at bd
    have tot := Set.ncard_add_ncard_compl W
    omega
  constructor
  · intro W
    simpa [retainedScore] using spec (W : Set X)
  · obtain ⟨S,best⟩ := tutte_berge_attained G
    refine ⟨Sᶜ.toFinset,?_⟩
    unfold retainedScore
    have setEq : (↑Sᶜ.toFinset : Set X) = Sᶜ := Set.coe_toFinset _
    have oddEq := congrArg (fun K : Set X => (G.induce K).oddComponents.ncard) setEq
    rw [oddEq,← Set.ncard_eq_toFinset_card',best]
    have := Set.ncard_add_ncard_compl S
    omega

#print axioms tutte_berge_attained
#print axioms max_retainedScore_exact
end JSP452Audit.StarHost
