import ZeroReserveIndependentCuts
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- Choose a cardinal-maximum independent set on the original finite labels.
This finite extremum is a proof-level choice, not an enumerative graph search. -/
theorem exists_largest_independent_set (G : SimpleGraph X) :
    ∃ I : Set X,G.IsIndepSet I ∧ ∀S : Set X,G.IsIndepSet S → S.ncard≤I.ncard := by
  classical
  let _ := Fintype.ofFinite (Set X)
  let C : Finset (Set X) := Finset.univ.filter (fun I => G.IsIndepSet I)
  have empty : G.IsIndepSet ∅ := by
    intro x hx
    exact hx.elim
  have present : C.Nonempty := ⟨∅,by simp [C,empty]⟩
  obtain ⟨I,hi,max⟩ := C.exists_max_image Set.ncard present
  refine ⟨I,(Finset.mem_filter.mp hi).2,?_⟩
  intro S hs
  exact max S (by simp [C,hs])

/-- Any existing independent triple persists as a cardinal lower bound on
the chosen largest independent set, on precisely the same graph. -/
theorem largest_independent_set_has_triple_size (G : SimpleGraph X)
    (triple : ∃S : Set X,S.ncard=3 ∧ G.IsIndepSet S) :
    ∃ I : Set X,G.IsIndepSet I ∧
      (∀S : Set X,G.IsIndepSet S → S.ncard≤I.ncard) ∧ 3≤I.ncard := by
  obtain ⟨I,ind,max⟩ := exists_largest_independent_set G
  obtain ⟨S,three,indS⟩ := triple
  have low := max S indS
  exact ⟨I,ind,max,by omega⟩

#print axioms exists_largest_independent_set
#print axioms largest_independent_set_has_triple_size
end JSP452Audit.StarHost
