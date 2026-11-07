import PhysicalCrossingsOfTheTwoNineBoxes
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
noncomputable def survivingSize {I X : Type*} [Finite X] (G : SimpleGraph X)
    (K : NinePortRegion G) (R : SimpleGraph X) (n : I→ℕ)
    (f : (forest n).Copy (R⊔restoredInternal G K))
    (i : ↥((whollyInternal G K R n f)ᶜ : Set I)) : ℕ := by
  classical exact if i.val∈touchedStars R (restoredInternal G K) n f then 1 else n i.val

theorem surviving_size_positive {I X : Type*} [Finite X] (G : SimpleGraph X)
    (K : NinePortRegion G) (R : SimpleGraph X) (n : I→ℕ) (pn : ∀i,1≤n i)
    (f : (forest n).Copy (R⊔restoredInternal G K))
    (i : ↥((whollyInternal G K R n f)ᶜ : Set I)) : 1≤survivingSize G K R n f i := by
  classical
  unfold survivingSize;split
  · exact le_rfl
  · exact pn _

theorem actual_surviving_copy {I X : Type*} [Finite X] (G : SimpleGraph X)
    (K : NinePortRegion G) (R : SimpleGraph X) (less : R≤eraseInternal G K.chosen) (n : I→ℕ)
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

#print axioms surviving_size_positive
#print axioms actual_surviving_copy
end JSP452Audit.StarHost.NinePortRegion
