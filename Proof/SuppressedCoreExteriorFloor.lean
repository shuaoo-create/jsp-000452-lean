import OriginalFullOppositeAtMostHalf
namespace JSP452Audit.StarHost
open SimpleGraph

def noRemovedLabel (s : ℕ) : RemovalBudget s :=
  ⟨{∅},⟨∅,Finset.mem_singleton_self _⟩⟩

theorem no_removed_length (s : ℕ) : (noRemovedLabel s).len=s := by
  simp [RemovalBudget.len,RemovalBudget.loss,noRemovedLabel]

/-- An internal graph uniformly below D cannot accommodate even one
star of the constant D list, at any of its original suffixes. -/
theorem below_full_admits_empty {s D : ℕ} {X : Type*} [Finite X] (H : SimpleGraph X)
    (small : ∀v,Nat.card (H.neighborSet v)<D) :
    AdmitsInternal (noRemovedLabel s) (fun _ : Fin s => D) H := by
  classical
  intro i l hl U hosts
  have empty : U=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    obtain ⟨f⟩ := hosts
    obtain ⟨one⟩ := oneStar_in_forest (fun _ : U => D) ⟨z,hz⟩
    let g := f.comp one
    have large := star_copy_center_degree H g
    have cap := small (g (center (fun _ : Fin 1 => D) 0))
    omega
  subst U
  simp [originalRemoved,noRemovedLabel]

theorem suppressed_core_exterior_floor {s t r D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (R : SimpleGraph K.core) (sub : R≤G.induce K.core)
    (small : ∀x,Nat.card (R.neighborSet x)<D) (η : ℕ) (light : matchingEdges ((G.induce K.core) \ R)≤η)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (hn : Antitone n) (hm : Antitone m) (pm : ∀j,1≤m j)
    (full : n ⟨0,hs⟩=D) (degree : 0<D) (row : ForcingRow G s t (padDemand n) (padDemand m) r) :
    ∀j,0<j → j≤D → t-(r+K.roots.ncard+η)≤uniformEnvelope (G.induce K.rest) j := by
  let N := fun _:Fin 1 => D
  let W := noRemovedLabel 1
  let V := componentBudget ((G.induce K.core) \ R) m
  let a := K.roots.ncard
  have red : AdmitsInternal W N R := below_full_admits_empty R small
  have mono : Antitone N := fun _ _ _ => le_rfl
  have pos : ∀i,1≤N i := fun _ => degree
  have keep (i:Fin 1) : N i≤padDemand n i.val := by
    have zero : i.val=0 := by have := i.isLt;omega
    change D≤padDemand n i.val;rw [zero,padDemand,dif_pos hs,full]
  have oneRow := shorten_left_complete_row G n N (padDemand m) hs keep row
  have out := two_budget_exterior_row G K R sub N m mono hm pos pm W V red
    (component_budget_admits _ m pm) oneRow
  have Wlen : W.len=1 := no_removed_length 1
  have fit : V.loss≤η := (component_budget_loss_le _ m).trans light
  intro j jpos cap
  by_cases live : 0<t-(r+a+η)
  · have llen : 0<V.len := by dsimp only [RemovalBudget.len];omega
    have active : 0<W.len := by omega
    have first : 0<originalThresholdCount (W.entries N) j := by
      apply (original_threshold_prefix (W.entries N) (W.entries_antitone N mono) j ⟨0,active⟩).1
      exact W.le_entries (fun _ => cap)
    have second := original_threshold_one (V.entries m) (V.entries_positive m pm)
    have actual := actual_rectangle_le_column (r:=r+a) (W.entries N) (V.entries m) (W.entries_antitone N mono) (V.entries_antitone m hm)
      (a:=j) (b:=1) (h:=j) (by omega) first (second.symm ▸ llen)
    rw [second] at actual
    have env := widthAt_le_uniformEnvelope active llen (W.entries N) (V.entries m) (W.entries_antitone N mono)
      (V.entries_antitone m hm) (W.entries_positive N pos) (V.entries_positive m pm) _ _ j out jpos
    change widthAt (W.entries N) (V.entries m) (r+a) j≤uniformEnvelope (G.induce K.rest) j at env
    have size : V.len=t-V.loss := rfl
    change t-(r+a+η)≤uniformEnvelope (G.induce K.rest) j;omega
  · change t-(r+a+η)≤_;omega

#print axioms no_removed_length
#print axioms below_full_admits_empty
#print axioms suppressed_core_exterior_floor
end JSP452Audit.StarHost