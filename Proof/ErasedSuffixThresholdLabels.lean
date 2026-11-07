import OneActualSurvivingForest
namespace JSP452Audit.StarHost

/-- Read the fixed budget list in the original suffix, retaining the
injection of positions into the actual non-internal labels. -/
theorem retained_budget_indices {s i l old : ℕ} (n : Fin s→ℕ) (W : RemovalBudget s)
    (length : i+old=s) (fits : i+l=W.len) (U : Set (Fin old))
    (legal : originalRemoved i old length.le Uᶜ∈W.choices) :
    ∃g:Fin l ↪ U,∀z,padDemand (W.entries n) (i+z.val)≤n (originalSuffixLabel i old length.le (g z).val) := by
  let T : ↥W.choices := ⟨_,legal⟩
  let p (z : Fin l) : Fin W.len := ⟨i+z.val,by have := z.isLt;omega⟩
  let x (z : Fin l) := W.label T (p z)
  have low (z : Fin l) : i≤(x z).val := by have h := W.label_ge T (p z);change i+z.val≤(x z).val at h;omega
  let loc (z : Fin l) : Fin old := ⟨(x z).val-i,by have := (x z).isLt;have := low z;omega⟩
  have atOriginal (z : Fin l) : originalSuffixLabel i old length.le (loc z)=x z := by
    apply Fin.ext;change i+((x z).val-i)=(x z).val;have := low z;omega
  have mem (z : Fin l) : loc z∈U := by
    by_contra lost
    exact W.label_kept T (p z) (Finset.mem_map.mpr ⟨loc z,(Set.Finite.mem_toFinset _).mpr lost,atOriginal z⟩)
  let g : Fin l ↪ U := {
    toFun := fun z => ⟨loc z,mem z⟩
    inj' := by
      intro a b eq
      have same := congrArg (fun u:U => originalSuffixLabel i old length.le u.val) eq
      change originalSuffixLabel i old length.le (loc a)=originalSuffixLabel i old length.le (loc b) at same
      rw [atOriginal,atOriginal] at same
      have q := (W.label T).injective same
      exact Fin.ext (Nat.add_left_cancel (congrArg Fin.val q)) }
  refine ⟨g,fun z => ?_⟩
  change padDemand (W.entries n) (i+z.val)≤n (originalSuffixLabel i old length.le (loc z))
  rw [atOriginal,padDemand,dif_pos (p z).isLt];exact W.entries_le n T (p z)

/-- Damaged indices may disappear. Outside them the actual surviving
labels are retained and their assigned heights meet the same threshold. -/
theorem many_in_retained_subtype {I : Type*} [Fintype I] {q b : ℕ} (f : Fin q ↪ I)
    (bad : Finset I) (price : bad.card≤b) (U : Set I) [Fintype U] (val : U→ℕ) (h : ℕ)
    (keep : ∀z,f z∉bad → f z∈U) (fit : ∀z (ok:f z∉bad),h≤val ⟨f z,keep z ok⟩) :
    q-b≤(Finset.univ.filter (fun u:U => h≤val u)).card := by
  classical
  let S := Finset.univ.map f
  let E := S \ bad
  let V := Finset.univ.filter (fun u:U => h≤val u)
  have size : S.card=q := by simp [S]
  have eq := Finset.card_sdiff_add_card_inter S bad
  have cost := Finset.card_le_card (Finset.inter_subset_right : S∩bad⊆bad)
  have retained (x:↥E) : ∃u:U,u.val=x.val ∧ u∈V := by
    obtain ⟨within,ok⟩ := Finset.mem_sdiff.mp x.property
    obtain ⟨z,_,same⟩ := Finset.mem_map.mp within
    have valid : f z∉bad := same ▸ ok
    exact ⟨⟨f z,keep z valid⟩,same,Finset.mem_filter.mpr ⟨Finset.mem_univ _,fit z valid⟩⟩
  let map (x:↥E) : ↥V := ⟨(retained x).choose,(retained x).choose_spec.2⟩
  have inj : Function.Injective map := by
    intro x y eq
    apply Subtype.ext
    exact (retained x).choose_spec.1.symm.trans ((congrArg (fun z:↥V => z.val.val) eq).trans (retained y).choose_spec.1)
  have count : E.card≤V.card := by simpa using Fintype.card_le_of_injective map inj
  change (S \ bad).card≤V.card at count
  change q-b≤V.card;omega

#print axioms retained_budget_indices
#print axioms many_in_retained_subtype
end JSP452Audit.StarHost
