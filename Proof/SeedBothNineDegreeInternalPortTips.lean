import FullDegreeExposureAfterRestoringLeaves
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

abbrev tips := Set.range (fun i => (R.port i).tip)

theorem chosen_full (cap : ∀x,Nat.card (G.neighborSet x)≤9) {v : X} (inside : v∈R.chosen) :
    Nat.card (G.neighborSet v)=9 := by
  have one (i : Fin 2) (mem : v∈R.box i) :=
    uniform_tight_piece_full G 3 6 cap R.K.S R.K.T (R.select i).val.val (R.select i).val.property v mem
  exact inside.elim (one 0) (one 1)

theorem two_tips_independent : R.tips⊆R.chosen ∧ G.IsIndepSet R.tips := by
  have sub : R.tips⊆R.chosen := by
    rintro _ ⟨i,rfl⟩;fin_cases i
    · exact Or.inl (R.port 0).tip_mem
    · exact Or.inr (R.port 1).tip_mem
  have no : ¬G.Adj (R.port 0).tip (R.port 1).tip := by
    intro e
    rcases R.box_separation 0 (R.port 0).tip_mem e with zero|root
    · exact Set.disjoint_left.mp R.disjoint_boxes zero (R.port 1).tip_mem
    · exact R.root_outside_box 0 1 (root ▸ (R.port 1).tip_mem)
  refine ⟨sub,?_⟩
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ ne edge
  fin_cases i <;> fin_cases j
  · exact ne rfl
  · exact no edge
  · exact no edge.symm
  · exact ne rfl

/-- A fixed independent full-degree set contains both actual port tips and
dominates all remaining vertices of the two selected boxes. -/
theorem internal_stage_with_both_tips (cap : ∀x,Nat.card (G.neighborSet x)≤9) :
    ∃I : Set X,R.tips⊆I ∧ I⊆R.chosen ∧ G.IsIndepSet I ∧
      (∀x∈I,Nat.card (G.neighborSet x)=9) ∧
      ∀x∈R.chosen,x∈I ∨ ∃y∈I,G.Adj x y := by
  let T := R.tips
  let V := {x | x∈R.chosen ∧ x∉T ∧ ∀y∈T,¬G.Adj x y}
  obtain ⟨J,sub,_,ind,dom⟩ := choose_full_exterior_independent G V 9
  obtain ⟨core,seed⟩ := R.two_tips_independent
  have inW : T∪J⊆R.chosen := Set.union_subset core (fun _ j => (sub j).1)
  refine ⟨T∪J,Set.subset_union_left,inW,?_,fun _ h => R.chosen_full cap (inW h),?_⟩
  · intro x hx y hy ne edge
    rcases hx with hx|hx <;> rcases hy with hy|hy
    · exact seed hx hy ne edge
    · exact (sub hy).2.2 x hx edge.symm
    · exact (sub hx).2.2 y hy edge
    · exact ind hx hy ne edge
  · intro x xin
    by_cases h : x∈T
    · exact Or.inl (Or.inl h)
    by_cases seen : ∃y∈T,G.Adj x y
    · obtain ⟨y,hy,e⟩ := seen;exact Or.inr ⟨y,Or.inl hy,e⟩
    · have eligible : x∈V := ⟨xin,h,fun y hy e => seen ⟨y,hy,e⟩⟩
      rcases dom x eligible (R.chosen_full cap xin) with inJ|⟨y,hy,e⟩
      · exact Or.inl (Or.inr inJ)
      · exact Or.inr ⟨y,Or.inr hy,e⟩

#print axioms chosen_full
#print axioms two_tips_independent
#print axioms internal_stage_with_both_tips
end JSP452Audit.StarHost.NinePortRegion
