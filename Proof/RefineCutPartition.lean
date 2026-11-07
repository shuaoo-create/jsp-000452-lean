import ActualCrossingPort
namespace JSP452Audit.StarHost
open SimpleGraph
variable {V J : Type*}

noncomputable def splitCutParts (W : J→Set V) (p : J) (L R : Set V) : Option J→Set V := by
  classical exact fun i => match i with
    | none => R
    | some j => if j=p then L else W j

/-- Replacing the preferred part by its two cut sides leaves pairwise
nonadjacent cliques on the residual labels other than the crossing endpoint. -/
theorem split_cut_parts_structure (H : SimpleGraph V) (W : J→Set V) (p : J) (x : V)
    (L R : Set V) (split : L∪R=W p \ {x}) (lr : Disjoint L R)
    (clL : H.IsClique L) (clR : H.IsClique R) (lrSep : ∀a∈L,∀b∈R,¬H.Adj a b)
    (xp : x∈W p) (apart : ∀i j,i≠j → Disjoint (W i) (W j)) (cover : ∀a,∃i,a∈W i)
    (cl : ∀i,i≠p → H.IsClique (W i))
    (sep : ∀i j,i≠p → j≠p → i≠j → ∀a∈W i,∀b∈W j,¬H.Adj a b)
    (port : ∀i,i≠p → ∀a∈W p,∀b∈W i,H.Adj a b → a=x) :
    let F := splitCutParts W p L R
    (∀i j,i≠j → Disjoint (F i) (F j)) ∧ (∀i,H.IsClique (F i)) ∧
    (∀i,x∉F i) ∧ (∀v,v≠x → ∃i,v∈F i) ∧
    (∀i j,i≠j → ∀a∈F i,∀b∈F j,¬H.Adj a b) := by
  intro F
  classical
  let own : Option J→J := fun i => i.getD p
  have sidesL : L⊆W p \ {x} := split ▸ Set.subset_union_left
  have sidesR : R⊆W p \ {x} := split ▸ Set.subset_union_right
  have sub (i : Option J) : F i⊆W (own i) := by
    cases i with
    | none => exact fun _ ha => (sidesR ha).1
    | some j =>
      by_cases eq : j=p
      · subst j; simpa [F,splitCutParts,own] using
          (show L⊆W p from fun _ ha => (sidesL ha).1)
      · simp [F,splitCutParts,own,eq]
  have off (i : Option J) : x∉F i := by
    cases i with
    | none => exact fun h => (sidesR h).2 (by simp)
    | some j =>
      by_cases eq : j=p
      · subst j; simpa [F,splitCutParts] using
          (show x∉L from fun h => (sidesL h).2 (by simp))
      · simpa [F,splitCutParts,eq] using
          (show x∉W j from fun h => Set.disjoint_left.mp (apart j p eq) h xp)
  have sides {i j : Option J} (diff : i≠j) (same : own i=own j) :
      (i=none ∧ j=some p) ∨ (j=none ∧ i=some p) := by
    cases i <;> cases j <;> simp_all [own]
  have apartF (i j : Option J) (diff : i≠j) : Disjoint (F i) (F j) := by
    by_cases same : own i=own j
    · rcases sides diff same with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · simpa [F,splitCutParts] using lr.symm
      · simpa [F,splitCutParts] using lr
    · exact (apart _ _ same).mono (sub i) (sub j)
  refine ⟨apartF,?_,off,?_,?_⟩
  · intro i
    cases i with
    | none => exact clR
    | some j =>
      by_cases eq : j=p
      · subst j; simpa [F,splitCutParts] using clL
      · simpa [F,splitCutParts,eq] using cl j eq
  · intro v ne
    obtain ⟨j,hj⟩ := cover v
    by_cases eq : j=p
    · subst j
      have hs : v∈L∪R := by rw [split]; exact ⟨hj,by simpa using ne⟩
      rcases hs with hl|hr
      · exact ⟨some p,by simpa [F,splitCutParts] using hl⟩
      · exact ⟨none,hr⟩
    · exact ⟨some j,by simpa [F,splitCutParts,eq] using hj⟩
  · intro i j diff a ha b hb edge
    by_cases same : own i=own j
    · rcases sides diff same with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
      · exact lrSep b (by simpa [F,splitCutParts] using hb) a ha edge.symm
      · exact lrSep a (by simpa [F,splitCutParts] using ha) b hb edge
    have ai := sub i ha
    have bj := sub j hb
    by_cases ip : own i=p
    · have eq := port (own j) (fun h => same (ip.trans h.symm)) a (ip ▸ ai) b bj edge
      exact off i (eq ▸ ha)
    by_cases jp : own j=p
    · have eq := port (own i) ip b (jp ▸ bj) a ai edge.symm
      exact off j (eq ▸ hb)
    exact sep _ _ ip jp same a ai b bj edge

#print axioms split_cut_parts_structure
end JSP452Audit.StarHost
