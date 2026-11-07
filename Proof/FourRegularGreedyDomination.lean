import FourGreedyBlueStep
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

/-- A nonempty white set admits a deterministic greedy choice whose actual
deletion strictly decreases its size and pays 26 units. -/
theorem four_greedy_progress (G : SimpleGraph X) (reg : ∀x,Nat.card (G.neighborSet x)=4)
    (U:Set X) (present : U.Nonempty) : ∃v:X,0<(fourHit G U v).ncard ∧
      fourPotential G (U\fourHit G U v)+26≤fourPotential G U := by
  classical
  obtain ⟨x,hx⟩ := present
  let score (w:X) := (fourHit G U w).ncard
  obtain ⟨w,_,best⟩ := Finset.exists_max_image Finset.univ score ⟨x,Finset.mem_univ _⟩
  have max (u:X) : score u≤score w := best _ (Finset.mem_univ _)
  have one : 0<score x := (Set.ncard_pos (Set.toFinite _)).2 ⟨x,Or.inl rfl,hx⟩
  have pos := one.trans_le (max x)
  by_cases white : ∃v∈U,score v=score w
  · obtain ⟨v,hv,eq⟩ := white
    exact ⟨v,(by change 0<score v;omega),four_greedy_white_gain G reg U v hv (score w) eq max⟩
  have notMem : w∉U := fun h => white ⟨w,h,rfl⟩
  have lower (v:X) (hv:v∈U) : score v<score w :=
    lt_of_le_of_ne (max v) (fun eq => white ⟨v,hv,eq⟩)
  exact ⟨w,pos,four_greedy_blue_gain G reg U ⟨x,hx⟩ w notMem (score w) rfl lower⟩

/-- Each original vertex in U is hit by a chosen label. Induction uses the
actual surviving set and terminates even when the graph has no vertices. -/
theorem four_regular_greedy_dominates (G : SimpleGraph X) (reg : ∀x,Nat.card (G.neighborSet x)=4) :
    ∃S:Set X,(∀v,v∈S ∨ ∃w∈S,G.Adj v w) ∧ 13*S.ncard≤5*Nat.card X := by
  classical
  have solve (k:ℕ) : ∀U:Set X,U.ncard=k → ∃S:Set X,(∀v∈U,v∈S ∨ ∃w∈S,G.Adj v w) ∧
      26*S.ncard≤fourPotential G U := by
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro U eq
      by_cases present : U.Nonempty
      · obtain ⟨v,pos,gain⟩ := four_greedy_progress G reg U present
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
          change fourPotential G R+26≤fourPotential G U at gain
          omega
      · exact ⟨∅,fun v hv => False.elim (present ⟨v,hv⟩),by simp⟩
  obtain ⟨S,hit,cost⟩ := solve (Set.univ:Set X).ncard Set.univ rfl
  refine ⟨S,fun v => hit v (Set.mem_univ _),?_⟩
  have start : fourPotential G Set.univ=10*Nat.card X := by simp [fourPotential,fourLabelSum]
  rw [start] at cost;omega

#print axioms four_greedy_progress
#print axioms four_regular_greedy_dominates
end JSP452Audit.StarHost
