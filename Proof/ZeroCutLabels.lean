import RootFiberReduction
namespace JSP452Audit.StarHost
variable {I Z W : Type*} [Finite I] [Finite Z] [Finite W]

/-- The cost at each surviving root after keeping exactly two outside holes
and deleting the selected clique vertex. -/
noncomputable def survivingRootLoad (f : Z→I) (A : I→Set W) (z₀ : Z) (w₁ w₂ : W) (j : I) : ℕ :=
  (ownerFiber f j \ {z₀}).ncard + (A j∩{w₁,w₂}).ncard

theorem select_zero_deletion_labels [Nonempty I] [Nonempty Z] (f : Z→I) (A : I→Set W) (D : ℕ)
    (large : 6≤D) (size : Nat.card Z=D)
    (degree : ∀i,(ownerFiber f i).ncard+(A i).ncard=D)
    (notAll : ∀i,(ownerFiber f i).ncard<D) :
    ∃i z z₀ w₁ w₂,f z=i ∧ z≠z₀ ∧ w₁≠w₂ ∧ w₁∈A i ∧ w₂∈A i ∧
      ∀j,j≠i → survivingRootLoad f A z₀ w₁ w₂ j≤D-2 := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨p,_,great⟩ := Finset.univ.exists_max_image (fun i => (ownerFiber f i).ncard)
    (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty)
  have biggest (j : I) := great j (Finset.mem_univ j)
  have twoBound (j : I) (w₁ w₂ : W) (ne : w₁≠w₂) : (A j∩{w₁,w₂}).ncard≤2 :=
    (Set.ncard_le_ncard Set.inter_subset_right).trans_eq (Set.ncard_pair ne)
  by_cases light : (ownerFiber f p).ncard≤D-2
  · obtain ⟨z,z₀,owner,diff,room⟩ := reduce_fibers_outside_largest f p D large size biggest
    obtain ⟨w₁,w₂,hw₁,hw₂,ne⟩ := (Set.one_lt_ncard_iff (Set.toFinite (A p))).mp (by
      have h := degree p;omega)
    refine ⟨p,z,z₀,w₁,w₂,owner,diff,ne,hw₁,hw₂,?_⟩
    intro j jp
    dsimp [survivingRootLoad]
    have h := room j jp
    have w := twoBound j w₁ w₂ ne
    omega
  · have countP : (ownerFiber f p).ncard=D-1 := by have high:=notAll p;omega
    have rem : (ownerFiber f p)ᶜ.ncard=1 := by rw [Set.ncard_compl,size,countP];omega
    obtain ⟨z,hz⟩ := Set.ncard_eq_one.mp rem
    let i := f z
    have outside : z∈(ownerFiber f p)ᶜ := hz ▸ (Set.mem_singleton z)
    have ip : i≠p := outside
    have others (a : Z) (h : f a≠p) : a=z := Set.mem_singleton_iff.mp
      (show a∈({z} : Set Z) from hz ▸ (show a∈(ownerFiber f p)ᶜ from h))
    have iOnly : ownerFiber f i={z} := by
      ext a
      constructor
      · intro aIn
        have eq : f a=i := aIn
        exact Set.mem_singleton_iff.mpr (others a (eq ▸ ip))
      · intro eq
        exact congrArg f (Set.mem_singleton_iff.mp eq)
    have iCount : (ownerFiber f i).ncard=1 := by rw [iOnly,Set.ncard_singleton]
    have aw : (A p).ncard=1 := by have h:=degree p;omega
    have left : 1<(A i \ A p).ncard := by
      have iDeg := degree i
      have rest := Set.ncard_sdiff_add_ncard (A i) (A p)
      have total := Set.ncard_le_ncard (show A i⊆ A i ∪ A p from Set.subset_union_left)
      omega
    obtain ⟨w₁,w₂,h₁,h₂,ne⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).mp left
    obtain ⟨z₀,pown⟩ := (Set.ncard_pos (Set.toFinite (ownerFiber f p))).mp (by omega)
    have diff : z≠z₀ := fun eq => ip ((congrArg f eq).trans pown)
    refine ⟨i,z,z₀,w₁,w₂,rfl,diff,ne,h₁.1,h₂.1,?_⟩
    intro j ji
    by_cases jp : j=p
    · subst j
      have none : A p ∩ {w₁,w₂}=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro w ⟨wp,(eq|eq)⟩
        · exact h₁.2 (eq ▸ wp)
        · exact h₂.2 ((Set.mem_singleton_iff.mp eq) ▸ wp)
      have removed := Set.ncard_sdiff_singleton_add_one pown
      dsimp [survivingRootLoad];rw [none,Set.ncard_empty];omega
    · have empty : ownerFiber f j=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro a ha
        have eq : f a=j := ha
        have az := others a (eq ▸ jp)
        exact ji (eq.symm.trans (congrArg f az))
      dsimp [survivingRootLoad]
      have rest := twoBound j w₁ w₂ ne
      simp only [empty,Set.empty_sdiff,Set.ncard_empty,Nat.zero_add]
      omega

#print axioms select_zero_deletion_labels
end JSP452Audit.StarHost
