import ActualCrossingRootLabels
namespace JSP452Audit.StarHost
open SimpleGraph

private def withCenter {a b : ℕ} (leaves : Fin a ↪ Fin b) : Fin (a+1) ↪ Fin (b+1) where
  toFun := Fin.cases 0 (fun j => (leaves j).succ)
  inj' := by
    intro x y
    refine Fin.cases ?_ (fun i => ?_) x <;> refine Fin.cases ?_ (fun j => ?_) y
    · intro _;rfl
    · intro eq;exact (Fin.succ_ne_zero _ eq.symm).elim
    · intro eq;exact (Fin.succ_ne_zero _ eq).elim
    · intro eq;exact congrArg Fin.succ (leaves.injective (Fin.succ_injective _ eq))

/-- A single surviving copy with explicitly selected leaf labels at
every retained center, including the chosen crossing root edge. -/
theorem selected_leaf_copy {I J X : Type*} {R H : SimpleGraph X}
    (n : I→ℕ) (m : J→ℕ) (idx : J ↪ I) (f : (forest n).Copy H)
    (leaves : ∀j,Fin (m j) ↪ Fin (n (idx j)))
    (edges : ∀j b,R.Adj (f (center n (idx j))) (f (leaf n ⟨idx j,leaves j b⟩))) :
    (forest m).IsContained R := by
  let sel : Vertices m ↪ Vertices n := Function.Embedding.sigmaMap idx (fun j => withCenter (leaves j))
  refine ⟨{toHom := {toFun := fun x => f (sel x),map_rel' := ?_},
            injective' := f.injective.comp sel.injective}⟩
  intro x y adj
  obtain ⟨p,eq⟩ := (edgeEquiv m).surjective ⟨s(x,y),(forest m).mem_edgeSet.mpr adj⟩
  have ends : s(center m p.1,leaf m p)=s(x,y) := congrArg Subtype.val eq
  rcases Sym2.eq_iff.mp ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact edges p.1 p.2
  · exact (edges p.1 p.2).symm

noncomputable def survivingSize {I X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (R : SimpleGraph X) (n : I→ℕ)
    (f : (forest n).Copy (R⊔restoredInternal G K))
    (i : ↥((whollyInternal G K R n f)ᶜ : Set I)) : ℕ := by
  classical exact if i.val∈touchedStars R (restoredInternal G K) n f then 1 else n i.val

theorem surviving_size_positive {I X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (R : SimpleGraph X) (n : I→ℕ) (pn : ∀i,1≤n i)
    (f : (forest n).Copy (R⊔restoredInternal G K))
    (i : ↥((whollyInternal G K R n f)ᶜ : Set I)) : 1≤survivingSize G K R n f i := by
  classical
  unfold survivingSize;split
  · exact le_rfl
  · exact pn _

theorem actual_surviving_copy {I X : Type*} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) (R : SimpleGraph X) (less : R≤eraseInternal G K.core) (n : I→ℕ)
    (f : (forest n).Copy (R⊔restoredInternal G K)) :
    (forest (survivingSize G K R n f)).IsContained R := by
  classical
  let U := (whollyInternal G K R n f)ᶜ
  let touch := touchedStars R (restoredInternal G K) n f
  let m := survivingSize G K R n f
  have choice (j:U) : ∃map : Fin (m j) ↪ Fin (n j.val),∀b,
      R.Adj (f (center n j.val)) (f (leaf n ⟨j.val,map b⟩)) := by
    by_cases hit : j.val∈touch
    · obtain ⟨b,_,edge⟩ := touched_external_root_edge G K R n f less j.property hit
      have size : m j=1 := if_pos hit
      let pick : Fin (m j) ↪ Fin (n j.val) :=
        ⟨fun _ => b,fun x y _ => Fin.ext (by have hx:=x.isLt;have hy:=y.isLt;omega)⟩
      exact ⟨pick,fun _ => edge⟩
    · have size : m j=n j.val := if_neg hit
      let pick : Fin (m j) ↪ Fin (n j.val) := Fin.castLEEmb size.le
      exact ⟨pick,fun b => untouched_star_edge R (restoredInternal G K) n f hit (pick b)⟩
  exact selected_leaf_copy n m (Function.Embedding.subtype _) f (fun j => (choice j).choose)
    (fun j => (choice j).choose_spec)

#print axioms selected_leaf_copy
#print axioms surviving_size_positive
#print axioms actual_surviving_copy
end JSP452Audit.StarHost
