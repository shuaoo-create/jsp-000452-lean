import FourCutMates
namespace JSP452Audit.StarHost
variable {I Z W : Type*} [Finite I] [Finite Z] [Finite W]

omit [Finite I] in
/-- For a four-point clique and a largest owner with at most two points,
retain a point it owns and remove a different point so that every other
owner retains at most one. -/
theorem four_light_fiber_choice [Nonempty Z] (f : Z→I) (p : I) (size : Nat.card Z=4)
    (biggest : ∀j,(ownerFiber f j).ncard≤(ownerFiber f p).ncard)
    (light : (ownerFiber f p).ncard≤2) :
    ∃z z₀,f z=p ∧ z≠z₀ ∧ ∀j,j≠p → (ownerFiber f j \ {z₀}).ncard≤1 := by
  classical
  let t := Classical.choice ‹Nonempty Z›
  have ht := Set.ncard_ne_zero_of_mem (show t∈ownerFiber f (f t) from rfl)
  have b := biggest (f t)
  obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite (ownerFiber f p))).mp (by omega)
  by_cases high : ∃j,j≠p ∧ 2≤(ownerFiber f j).ncard
  · obtain ⟨j,jp,jtwo⟩ := high
    have jSize := biggest j
    obtain ⟨z₀,h₀⟩ := (Set.ncard_pos (Set.toFinite (ownerFiber f j))).mp (by omega)
    have diff : z≠z₀ := fun eq => jp (h₀.symm.trans (eq ▸ hz))
    have dis := owner_fibers_disjoint f jp.symm
    have counted := Set.ncard_union_eq dis
    have all : ownerFiber f p∪ownerFiber f j=Set.univ := by
      apply Set.eq_of_subset_of_ncard_le (Set.subset_univ _)
      rw [Set.ncard_univ];omega
    refine ⟨z,z₀,hz,diff,?_⟩
    intro u up
    by_cases uj : u=j
    · subst u
      have lost := Set.ncard_sdiff_singleton_add_one h₀
      omega
    · have empty : ownerFiber f u=∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro y hy
        have joined : y∈ownerFiber f p∪ownerFiber f j := all ▸ Set.mem_univ _
        exact joined.elim (fun h => up (hy.symm.trans h)) (fun h => uj (hy.symm.trans h))
      simp [empty]
  · obtain ⟨z₀,_,apart⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show ({z} : Set Z).ncard<(Set.univ : Set Z).ncard by rw [Set.ncard_singleton,Set.ncard_univ,size];decide)
    refine ⟨z,z₀,hz,fun eq => apart eq.symm,?_⟩
    intro u up
    have upper := Set.ncard_le_ncard (show ownerFiber f u \ {z₀}⊆ownerFiber f u from Set.sdiff_subset)
    by_contra! h
    exact high ⟨u,up,by omega⟩

omit [Finite I] in
/-- In the light-fiber case, only the owners of the other two clique
points can be full. A full owner must see both retained holes. -/
theorem four_remaining_full_roots (f : Z→I) (A : I→Set W) (size : Nat.card Z=4)
    {p : I} {z z₀ : Z} (owner : f z=p) (diff : z≠z₀)
    (fiberBound : ∀j,j≠p → (ownerFiber f j \ {z₀}).ncard≤1)
    {a b : W} (ab : a≠b) :
    (∀j,j≠p → survivingRootLoad f A z₀ a b j≤3 ∧
      (survivingRootLoad f A z₀ a b j=3 → a∈A j ∧ b∈A j)) ∧
    {j | j≠p ∧ survivingRootLoad f A z₀ a b j=3}.ncard≤2 := by
  classical
  have lim (j : I) : (A j∩{a,b}).ncard≤2 :=
    (Set.ncard_le_ncard Set.inter_subset_right).trans_eq (Set.ncard_pair ab)
  have full (j : I) (jp : j≠p) (top : survivingRootLoad f A z₀ a b j=3) :
      (A j∩{a,b})={a,b} ∧ (ownerFiber f j \ {z₀}).Nonempty := by
    dsimp [survivingRootLoad] at top
    have h := fiberBound j jp
    have l := lim j
    refine ⟨Set.eq_of_subset_of_ncard_le Set.inter_subset_right ?_,(Set.ncard_pos (Set.toFinite _)).mp (by omega)⟩
    rw [Set.ncard_pair ab];omega
  constructor
  · intro j jp
    have h := fiberBound j jp
    have bnd := lim j
    refine ⟨by dsimp [survivingRootLoad];omega,fun top => ?_⟩
    have eq := (full j jp top).1
    exact ⟨(show a∈A j∩{a,b} by rw [eq];exact Or.inl rfl).1,
      (show b∈A j∩{a,b} by rw [eq];exact Or.inr rfl).1⟩
  · let E : Set Z := ({z,z₀} : Set Z)ᶜ
    have small : E.ncard=2 := by dsimp [E];rw [Set.ncard_compl,Set.ncard_pair diff,size]
    have sub : {j | j≠p ∧ survivingRootLoad f A z₀ a b j=3}⊆f '' E := by
      rintro j ⟨jp,top⟩
      obtain ⟨y,hy,yn⟩ := (full j jp top).2
      refine ⟨y,?_,hy⟩
      rintro (eq|eq)
      · exact jp (hy.symm.trans ((congrArg f eq).trans owner))
      · exact yn eq
    exact (Set.ncard_le_ncard sub).trans ((Set.ncard_image_le (f:=f) (s:=E)).trans_eq small)

#print axioms four_light_fiber_choice
#print axioms four_remaining_full_roots
end JSP452Audit.StarHost
