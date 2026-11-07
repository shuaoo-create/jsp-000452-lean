import CubicCompleteSquareGroups
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X I : Type*} [Fintype X] [Fintype I]

/-- Every actual terminal white set has a paid static cover. Removing a
group retains exactly the endpoint labels whose two white endpoints survive. -/
theorem CubicPairFamily.complete_residual_grouping (P:CubicPairFamily X I) (G:SimpleGraph X) (U:Set X)
    (degree:∀x∈U,fourWhiteDegree G U x≤2) (cap:∀x∈U,fourWhiteDegree G U x+P.degree U x≤3)
    (centers:∀j∈P.active U,∃w:X,G.Adj (P.left j) w ∧ G.Adj (P.right j) w) :
    ∃S:Set X,(∀x∈U,x∈S ∨ ∃w∈S,G.Adj x w) ∧ 5*S.ncard+P.residualCost G U≤5*U.ncard := by
  classical
  have solve (k:ℕ) : ∀V:Set X,V⊆U → V.ncard=k → ∃S:Set X,(∀x∈V,x∈S ∨ ∃w∈S,G.Adj x w) ∧
      5*S.ncard+P.residualCost G V≤5*V.ncard := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro V sub count
      have less (x:X) : fourWhiteDegree G V x≤fourWhiteDegree G U x :=
        Set.ncard_le_ncard (Set.inter_subset_inter_right _ sub)
      have degV (x:X) (hx:x∈V) : fourWhiteDegree G V x≤2 := (less x).trans (degree x (sub hx))
      have capV (x:X) (hx:x∈V) : fourWhiteDegree G V x+P.degree V x≤3 :=
        (Nat.add_le_add (less x) (P.degree_mono sub x)).trans (cap x (sub hx))
      have actual (j:I) (hj:j∈P.active V) := centers j (P.active_mono sub hj)
      by_cases small : ∀x∈V,fourWhiteDegree G V x≤1
      · exact P.matching_residual_paid G V capV small actual
      push Not at small
      obtain ⟨x,hx,two⟩ := small
      obtain ⟨T,A,within,nonempty,hit,fee⟩ :=
        P.paid_step_at_degree_two G V ⟨x,hx⟩ two degV capV actual
      let R := V\T
      have eq : T.ncard+R.ncard=V.ncard := by
        rw [←Set.ncard_union_eq (show Disjoint T R from Set.disjoint_sdiff_right),Set.union_comm]
        exact congrArg Set.ncard (Set.sdiff_union_of_subset within)
      have pos := (Set.ncard_pos (Set.toFinite _)).2 nonempty
      have shrink : R.ncard<k := by omega
      obtain ⟨S,cover,rest⟩ := ih R.ncard shrink R (Set.sdiff_subset.trans sub) rfl
      refine ⟨A∪S,?_,?_⟩
      · intro u vu
        by_cases inT:u∈T
        · rcases hit u inT with a|⟨w,wa,e⟩
          · exact Or.inl (Or.inl a)
          · exact Or.inr ⟨w,Or.inl wa,e⟩
        · rcases cover u ⟨vu,inT⟩ with b|⟨w,ws,e⟩
          · exact Or.inl (Or.inr b)
          · exact Or.inr ⟨w,Or.inr ws,e⟩
      · have union := Set.ncard_union_le A S
        change 5*A.ncard+P.residualCost G V≤5*T.ncard+P.residualCost G R at fee
        omega
  exact solve U.ncard U Set.Subset.rfl rfl

/-- A finite cubic host has a dominating set of size at most two fifths
of its order. The bound also holds for disconnected and empty graphs. -/
theorem cubic_regular_two_fifths (G:SimpleGraph X) (reg:∀x,Nat.card (G.neighborSet x)=3) :
    ∃S:Set X,(∀x,x∈S ∨ ∃w∈S,G.Adj x w) ∧ 5*S.ncard≤2*Nat.card X := by
  classical
  apply cubic_domination_of_terminal G reg
  intro U terminal
  let _ := Fintype.ofFinite ↥(cubicDoubleBlue G U)
  apply cubic_terminal_of_pair_grouping G U reg terminal
  intro P cap centers
  exact P.complete_residual_grouping G U (fun x _ => terminal x) cap centers

#print axioms CubicPairFamily.complete_residual_grouping
#print axioms cubic_regular_two_fifths
end JSP452Audit.StarHost
