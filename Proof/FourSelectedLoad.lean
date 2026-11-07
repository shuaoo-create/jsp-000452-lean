import FourFiberChoice
namespace JSP452Audit.StarHost
variable {I Z W : Type*} [Finite I] [Finite Z] [Finite W]

theorem select_four_deletion_labels [Nonempty I] [Nonempty Z] (f : Z→I) (A : I→Set W)
    (size : Nat.card Z=4)
    (degree : ∀i,(ownerFiber f i).ncard+(A i).ncard=4)
    (notAll : ∀i,(ownerFiber f i).ncard<4) :
    ∃i z z₀ w₁ w₂,f z=i ∧ z≠z₀ ∧ w₁≠w₂ ∧ w₁∈A i ∧ w₂∈A i ∧
      (∀j,j≠i → survivingRootLoad f A z₀ w₁ w₂ j≤3 ∧
        (survivingRootLoad f A z₀ w₁ w₂ j=3 → w₁∈A j ∧ w₂∈A j)) ∧
      {j | j≠i ∧ survivingRootLoad f A z₀ w₁ w₂ j=3}.ncard≤2 := by
  classical
  let _ := Fintype.ofFinite I
  obtain ⟨p,_,great⟩ := Finset.univ.exists_max_image (fun i => (ownerFiber f i).ncard)
    (Finset.univ_nonempty : (Finset.univ : Finset I).Nonempty)
  have biggest (j : I) := great j (Finset.mem_univ j)
  have twoBound (j : I) (w₁ w₂ : W) (ne : w₁≠w₂) : (A j∩{w₁,w₂}).ncard≤2 :=
    (Set.ncard_le_ncard Set.inter_subset_right).trans_eq (Set.ncard_pair ne)
  by_cases light : (ownerFiber f p).ncard≤2
  · obtain ⟨z,z₀,owner,diff,room⟩ := four_light_fiber_choice f p size biggest light
    obtain ⟨a,b,ha,hb,ab⟩ := (Set.one_lt_ncard_iff (Set.toFinite (A p))).mp (by
      have h := degree p;omega)
    exact ⟨p,z,z₀,a,b,owner,diff,ab,ha,hb,four_remaining_full_roots f A size owner diff room ab⟩
  · have countP : (ownerFiber f p).ncard=4-1 := by have high:=notAll p;omega
    have rem : (ownerFiber f p)ᶜ.ncard=1 := by rw [Set.ncard_compl,size,countP]
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
    have cheap : ∀ j : I,j≠i → survivingRootLoad f A z₀ w₁ w₂ j≤2 := by
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
    have empty : {j | j≠i ∧ survivingRootLoad f A z₀ w₁ w₂ j=3}=∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro j ⟨ji,eq⟩;have h:=cheap j ji;omega
    refine ⟨fun j ji => ⟨(cheap j ji).trans (by decide),fun eq => ?_⟩,?_⟩
    · have h := cheap j ji;omega
    · rw [empty,Set.ncard_empty];decide

#print axioms select_four_deletion_labels
end JSP452Audit.StarHost
