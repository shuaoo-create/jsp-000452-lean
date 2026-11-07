import CompleteStagesOnSameClosedExterior
namespace JSP452Audit.StarHost
open SimpleGraph

theorem three_edge_independent_complement {X:Type*} [Finite X] (H:SimpleGraph X)
    (edges:H.edgeSet.ncard=3) :
    ∃J:Set X,H.IsIndepSet J ∧ (∀v∉J,∃w∈J,H.Adj v w) ∧ 2≤Jᶜ.ncard ∧ Jᶜ.ncard≤3 := by
  classical
  obtain ⟨I,ind,greatest⟩ := exists_largest_independent_set H
  have dom := largest_independent_dominates H I ind greatest
  obtain ⟨T,eq,cover⟩ := H.vertexCoverNum_exists
  have price := H.vertexCoverNum_le_encard_edgeSet
  rw [←eq,←Set.coe_ncard_eq_encard,←Set.coe_ncard_eq_encard] at price
  have cheap : T.ncard≤H.edgeSet.ncard := by exact_mod_cast price
  have lower := greatest Tᶜ (H.isIndepSet_compl_iff_isVertexCover.mpr cover)
  have cT := Set.ncard_add_ncard_compl T
  have cI := Set.ncard_add_ncard_compl I
  have atMost : Iᶜ.ncard≤3 := by omega
  by_cases two : 2≤Iᶜ.ncard
  · exact ⟨I,ind,dom,two,atMost⟩
  have hit : H.IsVertexCover Iᶜ := H.isVertexCover_compl.mpr ind
  have non : (Iᶜ : Set X).Nonempty := by
    have positive : 0<H.edgeSet.ncard := by omega
    obtain ⟨e,mem⟩ := (Set.ncard_pos H.edgeSet.toFinite).mp positive
    induction e using Sym2.inductionOn with
    | _ x y =>
      rcases hit (H.mem_edgeSet.mp mem) with hx|hy
      · exact ⟨x,hx⟩
      · exact ⟨y,hy⟩
  have one : Iᶜ.ncard=1 := by have := (Set.ncard_pos (Iᶜ:Set X).toFinite).mpr non;omega
  obtain ⟨x,oneSet⟩ := Set.ncard_eq_one.mp one
  rw [oneSet] at hit
  have empty : H.induce {v|v≠x}=⊥ := by
    apply le_antisymm _ bot_le
    intro v w edge
    rcases hit edge with hv|hw
    · exact (v.property (Set.mem_singleton_iff.mp hv)).elim
    · exact (w.property (Set.mem_singleton_iff.mp hw)).elim
  have degree := card_neighbor_add_induce_edge_ncard H x
  rw [empty,SimpleGraph.edgeSet_bot,Set.ncard_empty,Nat.add_zero,edges] at degree
  let J := (H.neighborSet x)ᶜ
  have inside : x∈J := H.loopless.irrefl x
  have newInd : H.IsIndepSet J := by
    intro v hv w hw ne edge
    rcases hit edge with left|right
    · have same := Set.mem_singleton_iff.mp left;subst v;exact hw edge
    · have same := Set.mem_singleton_iff.mp right;subst w;exact hv edge.symm
  have size : Jᶜ.ncard=3 := by
    dsimp [J];rw [compl_compl];exact degree
  refine ⟨J,newInd,?_,by omega,by omega⟩
  intro v out
  have adj : H.Adj x v := Classical.not_not.mp out
  exact ⟨x,inside,adj.symm⟩

#print axioms three_edge_independent_complement
end JSP452Audit.StarHost
