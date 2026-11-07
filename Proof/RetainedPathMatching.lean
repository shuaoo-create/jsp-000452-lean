import ActualCliqueDeletion
import ThreePathCover
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem cross_on_induced_labels (Q : SimpleGraph X) (T I C : Set X) (R K : Set T)
    (hr : ∀v∈R,v.val∈I) (hk : ∀v∈K,v.val∈C) :
    crossCount (Q.induce T) R K ≤ crossCount Q I C := by
  let f (v : {p : (↥R × ↥K) // (Q.induce T).Adj p.1.val p.2.val}) :
      {p : (↥I × ↥C) // Q.Adj p.1.val p.2.val} :=
    ⟨(⟨v.val.1.val.val,hr _ v.val.1.property⟩,⟨v.val.2.val.val,hk _ v.val.2.property⟩),v.property⟩
  apply Nat.card_le_card_of_injective f
  intro v w eq
  apply Subtype.ext
  apply Prod.ext
  · exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.1.val) eq))
  · exact Subtype.ext (Subtype.ext (congrArg (fun z => z.val.2.val) eq))

private theorem loses_neighbor (Q : SimpleGraph X) (T : Set X) (v : T)
    (w : X) (outside : w∉T) (edge : Q.Adj v.val w) (D : ℕ)
    (reg : Nat.card (Q.neighborSet v.val)=D) :
    Nat.card ((Q.induce T).neighborSet v)≤D-1 := by
  have strict : Q.neighborSet v.val∩T ⊂ Q.neighborSet v.val := by
    refine ⟨Set.inter_subset_left,fun sub => outside ((sub edge).2)⟩
  have h := Set.ncard_lt_ncard strict
  rw [←Nat.card_coe_set_eq (Q.neighborSet v.val),reg] at h
  rw [induced_degree_intersection];omega

/-- Match the graph induced on exactly the roots, both leaves, and the
companion clique minus the selected vertex. -/
theorem retained_path_remainder (Q : SimpleGraph X) (I C : Set X) (a b x z : X)
    (D : ℕ) (six : 6≤D) (par : Even D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (ind : Q.IsIndepSet I) (dis : Disjoint I C) (ab : a≠b) (ar : a∉I) (br : b∉I)
    (ac : a∉C) (bc : b∉C) (zc : z∈C) (cl : Q.IsClique C) (order : C.ncard=D-1)
    (budget : crossCount Q I C≤D+1) (xa : Q.Adj x a) (xb : Q.Adj x b)
    (ln : (Q.neighborSet a∩I).ncard=D-1) (rn : (Q.neighborSet b∩I).ncard=D-1) :
    let T := I∪{a,b}∪(C\{z})
    x∉T → (∀i∈I,(Q.neighborSet i∩T).ncard≤D-1) → admits_matching_remainder (Q.induce T) (D-1) := by
  intro T xt rootCap
  classical
  let H := Q.induce T
  let R : Set T := {v | v.val∈I}
  let K : Set T := {v | v.val∈C\{z}}
  let l : T := ⟨a,Or.inl (Or.inr (by simp))⟩
  let r : T := ⟨b,Or.inl (Or.inr (by simp))⟩
  have zt : z∉T := by
    rintro ((hi|h)|h)
    · exact Set.disjoint_left.mp dis hi zc
    · rcases Set.mem_insert_iff.mp h with e|e
      · exact ac (e ▸ zc)
      · exact bc ((Set.mem_singleton_iff.mp e) ▸ zc)
    · exact h.2 (by simp)
  have cover (v:T) : v∈R ∨ v=l ∨ v=r ∨ v∈K := by
    rcases v.property with (hi|h)|h
    · exact Or.inl hi
    · rcases Set.mem_insert_iff.mp h with ha|hb
      · exact Or.inr (Or.inl (Subtype.ext ha))
      · exact Or.inr (Or.inr (Or.inl (Subtype.ext (Set.mem_singleton_iff.mp hb))))
    · exact Or.inr (Or.inr (Or.inr h))
  have ci : Disjoint R K := Set.disjoint_left.mpr (fun v hv hk => Set.disjoint_left.mp dis hv hk.1)
  have size : K.ncard=D-2 := by
    have image : Subtype.val '' K=C\{z} := by
      ext v
      exact ⟨fun ⟨w,hw,eq⟩ => eq ▸ hw,fun h => ⟨⟨v,Or.inr h⟩,h,rfl⟩⟩
    have n := (Set.ncard_image_of_injective _ Subtype.val_injective).symm.trans (congrArg Set.ncard image)
    have removed := Set.ncard_sdiff_singleton_add_one zc
    omega
  have evenK : Even K.ncard := by
    have e := Nat.even_iff.mp par
    rw [Nat.even_iff,size];omega
  have clique : H.IsClique K := by
    intro v hv w hw ne
    exact cl hv.1 hw.1 (fun eq => ne (Subtype.ext eq))
  have cap (v:T) : Nat.card (H.neighborSet v)≤D-1 := by
    rcases cover v with h|e|e|h
    · rw [show H=Q.induce T from rfl,induced_degree_intersection]
      exact rootCap v.val h
    · subst v; exact loses_neighbor Q T l x xt xa.symm D (reg _)
    · subst v; exact loses_neighbor Q T r x xt xb.symm D (reg _)
    · exact loses_neighbor Q T v z zt (cl h.1 zc (fun eq => h.2 (Set.mem_singleton_iff.mpr eq))) D (reg _)
  have rootCost := (cross_on_induced_labels Q T I C R K (fun _ h => h) (fun _ h => h.1)).trans budget
  have choices (v w:T) (degree : (Q.neighborSet v.val∩I).ncard=D-1) :
      ∃i∈R,i≠w ∧ H.Adj v i := by
    by_contra! nope
    have sub : Q.neighborSet v.val∩I ⊆ {w.val} := by
      intro i hi
      let t : T := ⟨i,Or.inl (Or.inl hi.2)⟩
      by_contra diff
      exact nope t hi.2 (fun eq => diff (Set.mem_singleton_iff.mpr (congrArg Subtype.val eq))) hi.1
    have h := Set.ncard_le_ncard sub
    rw [Set.ncard_singleton,degree] at h
    omega
  exact path_clique_matching_remainder H D six R K l r (fun eq => ab (congrArg Subtype.val eq))
    (fun _ hi _ hj ne edge => ind hi hj (fun eq => ne (Subtype.ext eq)) edge) ci ar br
    (fun h => ac h.1) (fun h => bc h.1) cover clique evenK size cap rootCost
    (fun w => choices l w ln) (fun w => choices r w rn)

#print axioms retained_path_remainder
end JSP452Audit.StarHost
