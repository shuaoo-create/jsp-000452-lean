import CubicTerminalPairAccounting
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

/-- Early greedy operations and a paid terminal on each actual remainder
give one genuine dominating set in the same cubic graph. -/
theorem cubic_domination_of_terminal (G:SimpleGraph X) (reg : ∀x,Nat.card (G.neighborSet x)=3)
    (finish : ∀U:Set X,(∀x,fourWhiteDegree G U x≤2) →
      ∃S:Set X,(∀x∈U,x∈S ∨ ∃w∈S,G.Adj x w) ∧ 5*S.ncard≤cubicGroupPotential G U) :
    ∃S:Set X,(∀x,x∈S ∨ ∃w∈S,G.Adj x w) ∧ 5*S.ncard≤2*Nat.card X := by
  classical
  have solve (k:ℕ) : ∀U:Set X,U.ncard=k → ∃S:Set X,(∀x∈U,x∈S ∨ ∃w∈S,G.Adj x w) ∧
      5*S.ncard≤cubicGroupPotential G U := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U eq
      rcases cubic_early_step G (fun x => (reg x).le) U with closed|⟨v,pos,gain⟩
      · exact finish U closed
      let A := fourHit G U v
      let R := U\A
      obtain ⟨sep,whole⟩ := four_hit_partition G U v
      have count : A.ncard+R.ncard=U.ncard := (Set.ncard_union_eq sep).symm.trans (congrArg Set.ncard whole)
      have shrink : R.ncard<k := by change 0<A.ncard at pos;omega
      obtain ⟨S,cover,cost⟩ := ih R.ncard shrink R rfl
      refine ⟨insert v S,?_,?_⟩
      · intro u hu
        by_cases inside:u∈A
        · rcases inside.1 with same|adj
          · exact Or.inl (Or.inl same)
          · exact Or.inr ⟨v,Set.mem_insert _ _,adj.symm⟩
        · rcases cover u ⟨hu,inside⟩ with mem|⟨w,ws,edge⟩
          · exact Or.inl (Set.mem_insert_of_mem _ mem)
          · exact Or.inr ⟨w,Set.mem_insert_of_mem _ ws,edge⟩
      · have up := Set.ncard_insert_le v S
        change cubicGroupPotential G R+5≤cubicGroupPotential G U at gain
        omega
  obtain ⟨S,hit,cost⟩ := solve (Set.univ:Set X).ncard Set.univ rfl
  refine ⟨S,fun x => hit x (Set.mem_univ _),?_⟩
  have start : cubicGroupPotential G Set.univ=2*Nat.card X := by simp [cubicGroupPotential,fourLabelSum]
  rwa [start] at cost

/-- The remaining combinatorial obligation can be restricted to ordinary
white paths and cycles and genuinely indexed pairs, with its matching base
already paid on the same labels. -/
theorem cubic_terminal_of_pair_grouping (G:SimpleGraph X) (U:Set X) [Fintype ↥(cubicDoubleBlue G U)]
    (reg : ∀x,Nat.card (G.neighborSet x)=3) (terminal : ∀x,fourWhiteDegree G U x≤2)
    (group : ∀P:CubicPairFamily X ↥(cubicDoubleBlue G U),
      (∀v∈U,fourWhiteDegree G U v+P.degree U v≤3) →
      (∀i∈P.active U,∃w:X,G.Adj (P.left i) w ∧ G.Adj (P.right i) w) →
      ∃S:Set X,(∀v∈U,v∈S ∨ ∃w∈S,G.Adj v w) ∧ 5*S.ncard+P.residualCost G U≤5*U.ncard) :
    ∃S:Set X,(∀v∈U,v∈S ∨ ∃w∈S,G.Adj v w) ∧ 5*S.ncard≤cubicGroupPotential G U := by
  obtain ⟨P,points,cap,card⟩ := cubic_terminal_pairs G U reg
  obtain ⟨S,hit,paid⟩ := group P cap (fun i _ => ⟨i.val,(points i).2.2⟩)
  have account := cubic_terminal_cost_identity G U P reg terminal card
  exact ⟨S,hit,by omega⟩

#print axioms cubic_domination_of_terminal
#print axioms cubic_terminal_of_pair_grouping
end JSP452Audit.StarHost
