import NoSingleRootOwner
namespace JSP452Audit.StarHost
variable {I Z : Type*} [Finite I] [Finite Z]

def ownerFiber (f : Z→I) (i : I) : Set Z := {z | f z=i}

omit [Finite I] [Finite Z] in
theorem owner_fibers_disjoint (f : Z→I) {i j : I} (ne : i≠j) :
    Disjoint (ownerFiber f i) (ownerFiber f j) := by
  exact Set.disjoint_left.mpr (fun {z} hi hj => ne (hi.symm.trans hj))

omit [Finite I] in
private theorem fiber_pair_bound (f : Z→I) (i j : I) (ne : i≠j) :
    (ownerFiber f i).ncard+(ownerFiber f j).ncard≤Nat.card Z := by
  have h := Set.ncard_le_ncard (Set.subset_univ (ownerFiber f i∪ownerFiber f j))
  rwa [Set.ncard_union_eq (owner_fibers_disjoint f ne),Set.ncard_univ] at h

omit [Finite I] in
private theorem fiber_triple_bound (f : Z→I) (p i j : I) (pi : p≠i) (pj : p≠j) (ij : i≠j) :
    (ownerFiber f p).ncard+(ownerFiber f i).ncard+(ownerFiber f j).ncard≤Nat.card Z := by
  have apart : Disjoint (ownerFiber f p ∪ ownerFiber f i) (ownerFiber f j) := by
    apply Set.disjoint_left.mpr
    rintro x (xp|xi) xj
    · exact Set.disjoint_left.mp (owner_fibers_disjoint f pj) xp xj
    · exact Set.disjoint_left.mp (owner_fibers_disjoint f ij) xi xj
  have h := Set.ncard_le_ncard (Set.subset_univ (ownerFiber f p∪ownerFiber f i∪ownerFiber f j))
  rwa [Set.ncard_union_eq apart,Set.ncard_union_eq (owner_fibers_disjoint f pi),Set.ncard_univ] at h

omit [Finite I] in
/-- Remove one clique point and reserve a distinct clique point owned by p.
All remaining fibers except that of p now have size at most D−4. -/
theorem reduce_fibers_outside_largest [Nonempty Z] (f : Z→I) (p : I) (D : ℕ)
    (large : 6≤D) (size : Nat.card Z=D)
    (biggest : ∀j,(ownerFiber f j).ncard≤(ownerFiber f p).ncard) :
    ∃z z₀,f z=p ∧ z≠z₀ ∧ ∀j,j≠p → (ownerFiber f j \ {z₀}).ncard≤D-4 := by
  classical
  let t := Classical.choice ‹Nonempty Z›
  have occupied := Set.ncard_ne_zero_of_mem (show t∈ownerFiber f (f t) from rfl)
  have pos := biggest (f t)
  obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite (ownerFiber f p))).mp (by omega)
  have upper (j) (jp : j≠p) : (ownerFiber f j).ncard≤D-3 := by
    have budget := fiber_pair_bound f p j jp.symm
    have bound := biggest j
    omega
  by_cases other : ∃j,j≠p ∧ D-4<(ownerFiber f j).ncard
  · obtain ⟨j,jp,heavy⟩ := other
    obtain ⟨z₀,hj⟩ := (Set.ncard_pos (Set.toFinite (ownerFiber f j))).mp (by omega)
    have diff : z≠z₀ := fun eq => jp (hj.symm.trans (eq ▸ hz))
    refine ⟨z,z₀,hz,diff,?_⟩
    intro a ap
    by_cases aj : a=j
    · subst a
      have bound := upper j jp
      have removed := Set.ncard_sdiff_singleton_add_one hj
      omega
    · have budget := fiber_triple_bound f p j a jp.symm ap.symm (Ne.symm aj)
      have bp := biggest j
      have small := Set.ncard_le_ncard (Set.sdiff_subset : ownerFiber f a \ {z₀}⊆ownerFiber f a)
      omega
  · obtain ⟨z₀,_,nz⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard
      (show ({z} : Set Z).ncard < (Set.univ : Set Z).ncard by rw [Set.ncard_singleton,Set.ncard_univ];omega)
    refine ⟨z,z₀,hz,fun eq => nz (Set.mem_singleton_iff.mpr eq.symm),?_⟩
    intro a ap
    have ha : (ownerFiber f a).ncard≤D-4 := by
      by_contra! h;exact other ⟨a,ap,h⟩
    exact (Set.ncard_le_ncard Set.sdiff_subset).trans ha

#print axioms reduce_fibers_outside_largest
end JSP452Audit.StarHost
