import CrossingForcesThreePath
namespace JSP452Audit.StarHost

/-- Choose a single clique vertex whose deletion lowers all surviving root
degrees to D−1 or less. At most one root can still have D neighbors. -/
theorem choose_clique_deletion {I Z : Type*} [Finite Z] [Nonempty Z]
    (F : I→Set Z) (leaves : I→ℕ) (D : ℕ) (large : 6≤D)
    (two : ∀ i, leaves i≤2) (cap : ∀ i, leaves i+(F i).ncard≤D)
    (pair : ∀i j,i≠j → (F i).ncard+(F j).ncard≤D+1) :
    ∃z : Z, ∀i,leaves i+(F i\{z}).ncard≤D-1 := by
  classical
  by_cases full : ∃ i, leaves i+(F i).ncard=D
  · obtain ⟨i,top⟩ := full
    have li := two i
    obtain ⟨z,hz⟩ := (Set.ncard_pos (Set.toFinite (F i))).mp (by omega)
    refine ⟨z,?_⟩
    intro j
    by_cases eq : j=i
    · subst j
      have removed := Set.ncard_sdiff_singleton_add_one hz
      omega
    · have b := pair j i eq
      have lj := two j
      have le := Set.ncard_le_ncard (show F j\{z}⊆F j from Set.sdiff_subset)
      omega
  · let z := Classical.choice ‹Nonempty Z›
    refine ⟨z,?_⟩
    intro j
    have ne : leaves j+(F j).ncard≠D := fun eq => full ⟨j,eq⟩
    have bound := cap j
    have le := Set.ncard_le_ncard (show F j\{z}⊆F j from Set.sdiff_subset)
    omega

/-- Match all full roots to the two leaves when each root can use at least one
leaf and no pair of full roots is forced onto the same leaf. -/
theorem assign_full_roots_to_leaves {I : Type*} (A B S : Set I)
    (a0 : A.Nonempty) (eA : ∀i,∃p∈A,p≠i) (eB : ∀i,∃q∈B,q≠i)
    (each : ∀i∈S,i∈A ∨ i∈B)
    (pairA : ∀i∈S,∀j∈S,i≠j → i∈A ∨ j∈A)
    (pairB : ∀i∈S,∀j∈S,i≠j → i∈B ∨ j∈B)
    (exhaust : ∀i∈S,∀j∈S,i≠j → ∀k∈S,k=i ∨ k=j) :
    ∃p∈A,∃q∈B,p≠q ∧ ∀k∈S,k=p ∨ k=q := by
  classical
  by_cases two : ∃i∈S,∃j∈S,i≠j
  · obtain ⟨i,hi,j,hj,ne⟩ := two
    have ui := each i hi
    have uj := each j hj
    have va := pairA i hi j hj ne
    have vb := pairB i hi j hj ne
    have arr : (i∈A ∧ j∈B) ∨ (j∈A ∧ i∈B) := by tauto
    rcases arr with ⟨ia,jb⟩|⟨ja,ib⟩
    · exact ⟨i,ia,j,jb,ne,exhaust i hi j hj ne⟩
    · exact ⟨j,ja,i,ib,ne.symm,fun k hk => (exhaust i hi j hj ne k hk).elim Or.inr Or.inl⟩
  by_cases any : S.Nonempty
  · obtain ⟨i,hi⟩ := any
    have sole (k) (hk : k∈S) : k=i := by
      by_contra ne
      exact two ⟨k,hk,i,hi,ne⟩
    rcases each i hi with ia|ib
    · obtain ⟨q,hq,ne⟩ := eB i
      exact ⟨i,ia,q,hq,ne.symm,fun k hk => Or.inl (sole k hk)⟩
    · obtain ⟨p,hp,ne⟩ := eA i
      exact ⟨p,hp,i,ib,ne,fun k hk => Or.inr (sole k hk)⟩
  obtain ⟨p,hp⟩ := a0
  obtain ⟨q,hq,ne⟩ := eB p
  exact ⟨p,hp,q,hq,ne.symm,fun k hk => False.elim (any ⟨k,hk⟩)⟩

#print axioms choose_clique_deletion
#print axioms assign_full_roots_to_leaves
end JSP452Audit.StarHost
