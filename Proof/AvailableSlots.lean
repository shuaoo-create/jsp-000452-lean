import CrossLift
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

/-- Real and dummy stubs based at one vertex. -/
abbrev Spec.Slots (v : V) := P.G.neighborSet v ⊕ Fin (P.padding v)

/-- Stubs available for local pairing after the given original red edges are selected. -/
abbrev Spec.Available (F : SimpleGraph V) (v : V) :=
  {i : P.Slots v // (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∉ (P.crossLift F).verts}

private abbrev Occupied (F : SimpleGraph V) (v : V) :=
  {i : P.Slots v // (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∈ (P.crossLift F).verts}

private def occupiedNeighbor (F : SimpleGraph V) (v : V) :
    Occupied P F v → F.neighborSet v
  | ⟨.inl w,h⟩ => ⟨w.val,h⟩
  | ⟨.inr _,h⟩ => False.elim h

private def occupiedEquiv (F : SimpleGraph V) (hF : F ≤ P.G) (v : V) :
    Occupied P F v ≃ F.neighborSet v where
  toFun := occupiedNeighbor P F v
  invFun w := ⟨.inl ⟨w.val,hF w.property⟩, w.property⟩
  left_inv := by
    rintro ⟨w | i,h⟩
    · rfl
    · exact False.elim h
  right_inv _ := rfl

theorem Spec.card_available (F : SimpleGraph V) (hF : F ≤ P.G) (v : V) :
    Nat.card (P.Available F v) = P.G.degree v + P.padding v - Nat.card (F.neighborSet v) := by
  classical
  have used := Nat.card_congr (occupiedEquiv P F hF v)
  have size : Nat.card (P.Slots v) = P.G.degree v + P.padding v := by
    rw [Spec.Slots, Nat.card_sum, Nat.card_fin, Nat.card_eq_fintype_card, P.G.card_neighborSet_eq_degree]
  have split : Nat.card (P.Available F v) = Nat.card (P.Slots v) - Nat.card (Occupied P F v) := by
    simp only [Spec.Available, Occupied, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [split, size, used]

/-- All locally available stubs embed in distinct vertices outside the cross matching. -/
def Spec.availableAt (F : SimpleGraph V) : (Σ v, P.Available F v) ↪ P.Vertex where
  toFun i := .inl ⟨i.1,i.2.val⟩
  inj' := by
    rintro ⟨v,⟨i,hi⟩⟩ ⟨w,⟨j,hj⟩⟩ h
    have he : (⟨v,i⟩ : P.Stub) = ⟨w,j⟩ := Sum.inl.inj h
    cases he
    rfl

@[simp] theorem Spec.availableAt_not_in_cross (F : SimpleGraph V) (i : Σ v, P.Available F v) :
    P.availableAt F i ∉ (P.crossLift F).verts := i.2.property

#print axioms Spec.card_available
#print axioms Spec.availableAt
#print axioms Spec.availableAt_not_in_cross
end JSP452Audit.Padded
