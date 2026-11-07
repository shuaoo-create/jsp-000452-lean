import GoodPortLayerDrop

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

private theorem remove_one_count (N : Set X) (u : X) :
    letI := Classical.propDecidable
    (N \ {u}).ncard + (if u ∈ N then 1 else 0) = N.ncard := by
  classical
  by_cases hit : u ∈ N
  · have count := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr hit)
    simpa [hit] using count
  · have dis : Disjoint N ({u}: Set X) := Set.disjoint_left.mpr (by
      intro y hy he; exact hit ((Set.mem_singleton_iff.mp he) ▸ hy))
    simp [hit,dis.sdiff_eq_left]

/-- Delete two specified distinct labels. Both original incidence indicators
are counted separately in a subtraction-free identity. -/
theorem degree_after_pair_cut (Q : SimpleGraph X) [DecidableRel Q.Adj] {v w : X} (ne : v ≠ w)
    (x : ↥(({v,w} : Set X)ᶜ)) :
    Nat.card ((Q.induce ({v,w} : Set X)ᶜ).neighborSet x) +
      (if Q.Adj x.val v then 1 else 0) + (if Q.Adj x.val w then 1 else 0) =
        Nat.card (Q.neighborSet x.val) := by
  classical
  let N := Q.neighborSet x.val
  let N' := (N \ {v}) \ {w}
  let equiv : ((Q.induce ({v,w} : Set X)ᶜ).neighborSet x) ≃ ↥N' := {
    toFun := fun u => ⟨u.val.val,⟨u.property,fun h => u.val.property (Or.inl (Set.mem_singleton_iff.mp h))⟩,
      fun h => u.val.property (Or.inr h)⟩
    invFun := fun u => ⟨⟨u.val,fun h => h.elim (fun hv => u.property.1.2 (Set.mem_singleton_iff.mpr hv))
      u.property.2⟩,u.property.1.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have first := remove_one_count N v
  have second := remove_one_count (N \ {v}) w
  have wmem : w ∈ N \ {v} ↔ Q.Adj x.val w := by simp [N,Ne.symm ne]
  have vmem : v ∈ N ↔ Q.Adj x.val v := Iff.rfl
  simp only [wmem] at second
  simp only [vmem] at first
  rw [Nat.card_congr equiv,Nat.card_coe_set_eq]
  change ((N \ {v}) \ {w}).ncard + _ + _ = N.ncard
  omega

/-- For a triangle-free regular complement, cutting the endpoints of a complement
edge yields degree D-1 somewhere and degree below D-1 somewhere else. -/
theorem pair_cut_degrees (Q : SimpleGraph X) (D c : ℕ)
    (reg : ∀ x, Nat.card (Q.neighborSet x) = D)
    (compReg : ∀ x, Nat.card (Qᶜ.neighborSet x) = c)
    (triangle : ∀ x y z, Qᶜ.Adj x y → Qᶜ.Adj y z → ¬ Qᶜ.Adj z x)
    (hC : 2 ≤ c) (order : 2*c+3 ≤ Nat.card X) {v w : X} (vw : Qᶜ.Adj v w) :
    let H := Q.induce ({v,w} : Set X)ᶜ
    (∀ x, Nat.card (H.neighborSet x) ≤ D-1) ∧
      (∃ x, Nat.card (H.neighborSet x) = D-1) ∧
      (∃ y, Nat.card (H.neighborSet y) < D-1) := by
  classical
  intro H
  have side (x : ↥(({v,w} : Set X)ᶜ)) : Q.Adj x.val v ∨ Q.Adj x.val w := by
    by_contra! both
    have xv : x.val ≠ v := fun h => x.property (Or.inl h)
    have xw : x.val ≠ w := fun h => x.property (Or.inr (Set.mem_singleton_iff.mpr h))
    exact triangle v w x.val vw ((Q.compl_adj _ _).mpr ⟨xw,both.2⟩).symm
      ((Q.compl_adj _ _).mpr ⟨xv,both.1⟩)
  have count (x : ↥(({v,w} : Set X)ᶜ)) :
      Nat.card (H.neighborSet x) + (if Q.Adj x.val v then 1 else 0) +
        (if Q.Adj x.val w then 1 else 0) = D := (degree_after_pair_cut Q vw.ne x).trans (reg _)
  refine ⟨?_,?_,?_⟩
  · intro x
    have loss := count x
    rcases side x with h | h <;> simp only [if_pos h] at loss <;> omega
  · have choice : ∃ x ∈ Qᶜ.neighborSet v, x≠w := by
      by_contra! no
      have sub : Qᶜ.neighborSet v ⊆ ({w}:Set X) := fun y hy => Set.mem_singleton_iff.mpr (no y hy)
      have le := Set.ncard_le_ncard sub
      have num : (Qᶜ.neighborSet v).ncard = c := compReg v
      rw [num,Set.ncard_singleton] at le; omega
    obtain ⟨x,edge,xw⟩ := choice
    have xv : x≠v := (show Qᶜ.Adj v x from edge).ne.symm
    let u : ↥(({v,w}:Set X)ᶜ) := ⟨x,by simp [xv,xw]⟩
    have no : ¬ Q.Adj u.val v := (Q.compl_adj _ _).mp (show Qᶜ.Adj x v from (show Qᶜ.Adj v x from edge).symm) |>.2
    have yes := (side u).resolve_left no
    have loss := count u; simp only [if_neg no,if_pos yes] at loss
    exact ⟨u,by omega⟩
  · let A := Qᶜ.neighborSet v
    let B := Qᶜ.neighborSet w
    have dis : Disjoint A B := Set.disjoint_left.mpr (by
      intro x va wb
      exact triangle v w x vw wb (show Qᶜ.Adj v x from va).symm)
    have sz : (A ∪ B).ncard = c+c := by
      rw [Set.ncard_union_eq dis]
      exact congrArg₂ (·+·) (compReg v) (compReg w)
    have lt : (A ∪ B).ncard < (Set.univ : Set X).ncard := by rw [Set.ncard_univ,sz]; omega
    obtain ⟨y,_,outside⟩ := Set.exists_mem_notMem_of_ncard_lt_ncard lt
    have yv : y≠v := fun h => outside (Or.inr (h.symm ▸ vw.symm))
    have yw : y≠w := fun h => outside (Or.inl (h.symm ▸ vw))
    let u : ↥(({v,w}:Set X)ᶜ) := ⟨y,by simp [yv,yw]⟩
    have towardV : Q.Adj y v := by
      by_contra no
      exact outside (Or.inl (((Q.compl_adj _ _).mpr ⟨yv,no⟩).symm))
    have towardW : Q.Adj y w := by
      by_contra no
      exact outside (Or.inr (((Q.compl_adj _ _).mpr ⟨yw,no⟩).symm))
    have loss := count u
    change Nat.card (H.neighborSet u) + (if Q.Adj y v then 1 else 0) + (if Q.Adj y w then 1 else 0) = D at loss
    simp only [if_pos towardV,if_pos towardW] at loss
    exact ⟨u,by omega⟩

omit [Finite X] in
/-- A missing edge of the original graph supplies distinct cut endpoints. -/
theorem exists_complement_edge_of_ne_top (Q : SimpleGraph X) (noncomplete : Q ≠ ⊤) :
    ∃ v w, Qᶜ.Adj v w := by
  by_contra! no
  apply noncomplete
  apply top_unique
  intro v w distinct
  by_contra absent
  exact no v w ((Q.compl_adj v w).mpr ⟨distinct,absent⟩)

#print axioms exists_complement_edge_of_ne_top
#print axioms degree_after_pair_cut
#print axioms pair_cut_degrees
end JSP452Audit.StarHost
