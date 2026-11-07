import LocalEdges
import ChooseParity
import PoolComplete

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Size of the initial interval of optional tokens paired at an owner. -/
private noncomputable def mayBound (F : SimpleGraph V) (v : V) : ℕ :=
  min (Nat.card (P.Available F v) - min (Nat.card (P.Available F v)) (P.mandatoryCount v))
    (P.optionalCount v)

private theorem usedIndex_val (F : SimpleGraph V) (v : V) (j : P.MayIndex F v) :
    ((P.localChoice F v).optionalToken j).val = j.val := by
  change 0 + j.val = j.val
  exact Nat.zero_add _

/-- The carrier of the auxiliary graph changes with the bit; the availability
    predicate on the same local stub does not. No assumption on F is needed. -/
private theorem availableCard_invariant (F : SimpleGraph V) (b : Bool) (v : V) :
    Nat.card ((P.withPoolBit b).Available F v) = Nat.card (P.Available F v) := by
  let Q := P.withPoolBit b
  have same (i : P.Slots v) :
      (Sum.inl (⟨v,i⟩ : Q.Stub) : Q.Vertex) ∉ (Q.crossLift F).verts ↔
      (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∉ (P.crossLift F).verts := by
    cases i <;> rfl
  exact Nat.card_congr {
    toFun := fun i => ⟨i.val, (same i.val).mp i.property⟩
    invFun := fun i => ⟨i.val, (same i.val).mpr i.property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

private theorem mayBound_invariant (F : SimpleGraph V) (b : Bool) (v : V) :
    mayBound (P.withPoolBit b) F v = mayBound P F v := by
  unfold mayBound
  rw [availableCard_invariant P F b v]
  rfl

private theorem noLocalLeftToken (F : SimpleGraph V) (t : P.Token) :
    (Sum.inr t : P.Vertex) ∉ Set.range (P.localLeft F) := by
  rintro ⟨i, hi⟩
  change (Sum.inl _ : P.Vertex) = .inr t at hi
  cases hi

private theorem optional_used_iff (F : SimpleGraph V) (a : P.Optional) :
    P.optional a ∈ (P.crossLift F ⊔ P.localLift F).verts ↔ a.2.val < mayBound P F a.1 := by
  constructor
  · rintro (h | hl | ⟨⟨v, i | j⟩, hr⟩)
    · exact (P.token_not_mem_crossLift F _ h).elim
    · exact (noLocalLeftToken P F _ hl).elim
    · rw [P.localRight_mandatory F v i] at hr
      cases hr
    · rw [P.localRight_optional F v j] at hr
      have ho : (⟨v,(P.localChoice F v).optionalToken j⟩ : P.Optional) = a :=
        Sum.inr.inj (Sum.inl.inj (Sum.inr.inj hr))
      subst a
      simpa only [usedIndex_val] using
        (show ((P.localChoice F v).optionalToken j).val < mayBound P F v from
          (usedIndex_val P F v j).symm ▸ j.isLt)
  · obtain ⟨v,k⟩ := a
    intro hi
    let j : P.MayIndex F v := ⟨k.val,hi⟩
    have htok : (P.localChoice F v).optionalToken j = k :=
      Fin.ext (usedIndex_val P F v j)
    exact Or.inr (Or.inr ⟨⟨v,.inr j⟩, (P.localRight_optional F v j).trans
      (congrArg (fun i => P.optional ⟨v,i⟩) htok)⟩)

private theorem global_unmatched (F : SimpleGraph V) (g : Fin (if P.extra then 1 else 0)) :
    P.globalToken g ∉ (P.crossLift F ⊔ P.localLift F).verts := by
  rintro (h | hl | ⟨⟨v, i | j⟩, hr⟩)
  · exact P.token_not_mem_crossLift F _ h
  · exact noLocalLeftToken P F _ hl
  · rw [P.localRight_mandatory F v i] at hr
    cases hr
  · rw [P.localRight_optional F v j] at hr
    cases hr

theorem Spec.exists_even_freePool_cross_local (F : SimpleGraph V) :
    ∃ b : Bool, let Q := P.withPoolBit b
      Even (Nat.card (Q.FreePool (Q.crossLift F ⊔ Q.localLift F))) := by
  let U : P.Optional → Prop := fun a => mayBound P F a.1 ≤ a.2.val
  let Q := P.withEvenPool U
  refine ⟨P.poolBit U, ?_⟩
  apply P.even_chosenPool_of_iff U
    (fun t => Q.inPool t ∧ (Sum.inr t : Q.Vertex) ∉ (Q.crossLift F ⊔ Q.localLift F).verts)
  rintro ((a | a) | g)
  · exact ⟨fun h => h.1.elim, fun h => h.1.elim⟩
  · change (True ∧ Q.optional a ∉ (Q.crossLift F ⊔ Q.localLift F).verts) ↔
      True ∧ mayBound P F a.1 ≤ a.2.val
    rw [optional_used_iff Q F a, not_lt, mayBound_invariant P F (P.poolBit U) a.1]
  · exact ⟨fun _ => ⟨trivial,trivial⟩, fun _ => ⟨trivial, global_unmatched Q F g⟩⟩

#print axioms Spec.exists_even_freePool_cross_local
end JSP452Audit.Padded
