import PaddedGraph
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded

variable {V : Type*}

/-- Only the global parity token changes; all locally owned types remain definitionally equal. -/
abbrev Spec.withPoolBit (P : Spec V) (b : Bool) : Spec V := {P with extra := b}

variable [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

theorem Spec.withPoolBit_local_data (b : Bool) :
    (P.withPoolBit b).G = P.G ∧ (P.withPoolBit b).A = P.A ∧
    (P.withPoolBit b).B = P.B ∧ (P.withPoolBit b).padding = P.padding ∧
    (P.withPoolBit b).mandatoryCount = P.mandatoryCount ∧
    (P.withPoolBit b).optionalCount = P.optionalCount := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Retain exactly the indicated optional tokens and every global token. -/
def Spec.keepInPool (U : P.Optional → Prop) : P.Token → Prop
  | .inl (.inl _) => False
  | .inl (.inr o) => U o
  | .inr _ => True

abbrev Spec.ResidualPool (U : P.Optional → Prop) :=
  {t : P.Token // P.inPool t ∧ P.keepInPool U t}

/-- A decomposition of the actual token subtype, not merely a cardinal identity. -/
def Spec.residualPoolEquiv (U : P.Optional → Prop) :
    P.ResidualPool U ≃ ({o : P.Optional // U o} ⊕ Fin (if P.extra then 1 else 0)) where
  toFun
    | ⟨.inl (.inl _), ht⟩ => False.elim ht.1
    | ⟨.inl (.inr o), ht⟩ => .inl ⟨o, ht.2⟩
    | ⟨.inr j, _⟩ => .inr j
  invFun
    | .inl o => ⟨.inl (.inr o.1), trivial, o.2⟩
    | .inr j => ⟨.inr j, trivial, trivial⟩
  left_inv := by
    rintro ⟨((m | o) | j), h⟩
    · exact False.elim h.1
    · rfl
    · rfl
  right_inv := by
    rintro (⟨o, hu⟩ | j) <;> rfl

theorem Spec.card_residualPool (U : P.Optional → Prop) :
    Nat.card (P.ResidualPool U) =
      Nat.card {o : P.Optional // U o} + (if P.extra then 1 else 0) := by
  rw [Nat.card_congr (P.residualPoolEquiv U), Nat.card_sum, Nat.card_fin]

/-- Add one token if and only if the number of remaining local options is odd. -/
noncomputable def Spec.poolBit (U : P.Optional → Prop) : Bool :=
  decide (Nat.card {o : P.Optional // U o} % 2 = 1)

noncomputable abbrev Spec.withEvenPool (U : P.Optional → Prop) : Spec V :=
  P.withPoolBit (P.poolBit U)

theorem Spec.card_chosenPool (U : P.Optional → Prop) :
    Nat.card ((P.withEvenPool U).ResidualPool U) =
      Nat.card {o : P.Optional // U o} + (if P.poolBit U then 1 else 0) :=
  (P.withEvenPool U).card_residualPool U

theorem Spec.even_chosenPool (U : P.Optional → Prop) :
    Even (Nat.card ((P.withEvenPool U).ResidualPool U)) := by
  rw [P.card_chosenPool U, Nat.even_iff]
  by_cases h : Nat.card {o : P.Optional // U o} % 2 = 1
  · simp [Spec.poolBit, h, Nat.add_mod]
  · simp [Spec.poolBit, h]
    omega

/-- Feed a concrete remaining-token predicate to the parity argument, once its
membership is identified. This allows the previous partial matching to be supplied later. -/
theorem Spec.even_chosenPool_of_iff (U : P.Optional → Prop)
    (remaining : (P.withEvenPool U).Token → Prop)
    (mem_iff : ∀ t, remaining t ↔
      (P.withEvenPool U).inPool t ∧ (P.withEvenPool U).keepInPool U t) :
    Even (Nat.card {t // remaining t}) := by
  have h := funext fun t => propext (mem_iff t)
  rw [h]
  exact P.even_chosenPool U

#print axioms Spec.withPoolBit_local_data
#print axioms Spec.residualPoolEquiv
#print axioms Spec.card_residualPool
#print axioms Spec.card_chosenPool
#print axioms Spec.even_chosenPool
#print axioms Spec.even_chosenPool_of_iff

end JSP452Audit.Padded
