import TheOriginalFullProfileCannotBePaidOnTheSameExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem core_component_menu_totals {B:Type u} [Finite B] (C:SimpleGraph B) [Fintype C.ConnectedComponent] :
    matchingEdges C=∑i:C.ConnectedComponent,matchingEdges i.toSimpleGraph := by
  classical
  let ids := Function.Embedding.refl C.ConnectedComponent
  have add := (original_component_menu_accounts C ids Finset.univ).1
  have all : Finset.univ.sup (fun i:C.ConnectedComponent => labelledPart C (ids i))=C := by
    apply le_antisymm (Finset.sup_le (fun i _ _ _ h => h.1))
    intro x y e
    exact (Finset.le_sup (f:=fun i:C.ConnectedComponent => labelledPart C (ids i))
      (Finset.mem_univ (C.connectedComponentMk x))) (show (labelledPart C _).Adj x y from ⟨e,rfl⟩)
  rw [all] at add
  exact add

theorem sum_row_whole_component_menu {A B:Type u} [Finite A] [Finite B] (Y:SimpleGraph A) (C:SimpleGraph B)
    [Fintype C.ConnectedComponent] [DecidableEq C.ConnectedComponent] {s t r:ℕ} (n m:ℕ→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i<s,0<n i) (pm:∀i<t,0<m i)
    (row:ForcingRow (Y⊕g C) s t n m r)
    (menu:SplitCapacities (fun i:C.ConnectedComponent => matchingEdges i.toSimpleGraph) r) :
    ForcingRow Y s t n m (r+matchingEdges C) := by
  classical
  let part (i:C.ConnectedComponent) := (⊥:SimpleGraph A)⊕g labelledPart C i
  let out := Y⊕g (⊥:SimpleGraph B)
  have sub (i:C.ConnectedComponent) : part i≤Y⊕g C := by
    rintro (x|x) (y|y) h
    · exact h.elim
    · exact h
    · exact h
    · exact h.1
  have visible : out≤Y⊕g C := by
    rintro (x|x) (y|y) h
    · exact h
    · exact h
    · exact h
    · exact h.elim
  have cover : Y⊕g C≤out⊔Finset.univ.sup part := by
    rintro (x|x) (y|y) h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr ((Finset.le_sup (f:=part) (Finset.mem_univ (C.connectedComponentMk x)))
        (show (part (C.connectedComponentMk x)).Adj (Sum.inr x) (Sum.inr y) from ⟨h,rfl⟩))
  have price (i:C.ConnectedComponent) : matchingEdges (part i)=matchingEdges i.toSimpleGraph := by
    have eq := (original_component_menu_accounts C (Function.Embedding.refl _) ({i}:Finset C.ConnectedComponent)).1
    simp only [Finset.sup_singleton,Finset.sum_singleton,Function.Embedding.refl_apply] at eq
    change matchingEdges ((⊥:SimpleGraph A)⊕g labelledPart C i)=_
    rw [matchingEdges_sumGraph,matchingEdges_bot,Nat.zero_add]
    exact eq
  have ranks (T:Finset C.ConnectedComponent) : matchingEdges (T.sup part)≤∑i∈T,matchingEdges i.toSimpleGraph := by
    simpa only [price] using subfamily_rank_le_sum part T
  have next := realized_capacity_menu_row (Y⊕g C) out part _ n m hn hm visible sub cover ranks menu row
  rw [←core_component_menu_totals C] at next
  exact remove_isolated_summand_row Y n m pn pm next

#print axioms core_component_menu_totals
#print axioms sum_row_whole_component_menu
end JSP452Audit.StarHost
