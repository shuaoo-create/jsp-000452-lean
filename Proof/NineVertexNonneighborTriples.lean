import LastComponentPackingObstruction
namespace JSP452Audit.StarHost
open SimpleGraph

theorem nonneighbor_sets_agree_at_nine {X:Type*} [Finite X] (Q:SimpleGraph X) (order:Nat.card X=9)
    (reg:∀v,Nat.card (Q.neighborSet v)=6) (stages:∀A:Set X,CompleteDegreeStage Q 6 A → 3≤A.ncard) :
    ∀x y,¬Q.Adj x y → (Q.neighborSet x)ᶜ=(Q.neighborSet y)ᶜ := by
  classical
  have size (v:X) : (Q.neighborSet v)ᶜ.ncard=3 := by
    have total := Set.ncard_add_ncard_compl (Q.neighborSet v)
    have deg : (Q.neighborSet v).ncard=6 := reg v
    omega
  intro x y missing
  by_cases same:x=y
  · subst y;rfl
  have third : ∃z:X,z≠x ∧ z≠y ∧ ¬Q.Adj x z ∧ ¬Q.Adj y z := by
    by_contra! none
    let A : Set X := {x,y}
    have indep : Q.IsIndepSet A := by
      intro v hv w hw ne adj
      rcases hv with (eq|eq) <;> rcases hw with (eq'|eq')
      · exact ne (eq.trans eq'.symm)
      · exact missing (eq ▸ (Set.mem_singleton_iff.mp eq') ▸ adj)
      · exact missing ((Set.mem_singleton_iff.mp eq) ▸ eq' ▸ adj.symm)
      · exact ne ((Set.mem_singleton_iff.mp eq).trans (Set.mem_singleton_iff.mp eq').symm)
    have stage : CompleteDegreeStage Q 6 A := by
      refine ⟨indep,fun v _ => reg v,?_⟩
      intro v _
      by_cases hit:v∈A
      · exact Or.inl hit
      · have nx : v≠x := fun eq => hit (eq ▸ Set.mem_insert _ _)
        have ny : v≠y := fun eq => hit (eq ▸ Set.mem_insert_of_mem _ (Set.mem_singleton _))
        by_cases near : Q.Adj x v
        · exact Or.inr ⟨x,Set.mem_insert _ _,near.symm⟩
        · exact Or.inr ⟨y,Set.mem_insert_of_mem _ (Set.mem_singleton _),(none v nx ny near).symm⟩
    have limit := stages A stage
    have count : A.ncard=2 := Set.ncard_pair same
    omega
  obtain ⟨z,zx,zy,xz,yz⟩ := third
  let T : Set X := {x,y,z}
  have card : T.ncard=3 := by simp [T,same,zx.symm,zy.symm]
  have lx : T⊆(Q.neighborSet x)ᶜ := by
    rintro v (rfl|rfl|eq)
    · exact Q.loopless.irrefl _
    · exact missing
    · exact (Set.mem_singleton_iff.mp eq) ▸ xz
  have ly : T⊆(Q.neighborSet y)ᶜ := by
    rintro v (rfl|rfl|eq)
    · exact fun adj => missing adj.symm
    · exact Q.loopless.irrefl _
    · exact (Set.mem_singleton_iff.mp eq) ▸ yz
  have ex := Set.eq_of_subset_of_ncard_le lx ((size x).trans_le card.symm.le)
  have ey := Set.eq_of_subset_of_ncard_le ly ((size y).trans_le card.symm.le)
  exact ex.symm.trans ey

#print axioms nonneighbor_sets_agree_at_nine
end JSP452Audit.StarHost
