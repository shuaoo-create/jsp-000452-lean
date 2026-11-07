import AvailableSlots
import LocalPairCounts
import GreedyIndex
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit.Padded

variable {V : Type*} [Fintype V] (P : Spec V) [DecidableRel P.G.Adj]

abbrev Spec.FreeMust (M : P.graph.Subgraph) (v : V) :=
  {i : Fin (P.mandatoryCount v) // P.mandatory ⟨v,i⟩ ∉ M.verts}

abbrev Spec.FreeSlot (M : P.graph.Subgraph) (v : V) :=
  {i : P.Slots v // (Sum.inl (⟨v,i⟩ : P.Stub) : P.Vertex) ∉ M.verts}

/-- Once all pool tokens have been used, each unmatched vertex has a unique
    original owner and is either one of its slots or a mandatory token. -/
def Spec.freeEquiv (M : P.graph.Subgraph)
    (pool : ∀ t : P.Token, P.inPool t → (.inr t : P.Vertex) ∈ M.verts) :
    ((Σ v, P.FreeMust M v) ⊕ (Σ v, P.FreeSlot M v)) ≃ {x : P.Vertex // x ∉ M.verts} where
  toFun
    | .inl ⟨v,i⟩ => ⟨P.mandatory ⟨v,i.val⟩,i.property⟩
    | .inr ⟨v,i⟩ => ⟨.inl ⟨v,i.val⟩,i.property⟩
  invFun
    | ⟨.inl ⟨v,i⟩,h⟩ => .inr ⟨v,⟨i,h⟩⟩
    | ⟨.inr (.inl (.inl ⟨v,i⟩)),h⟩ => .inl ⟨v,⟨i,h⟩⟩
    | ⟨.inr (.inl (.inr j)),h⟩ => False.elim (h (pool (.inl (.inr j)) trivial))
    | ⟨.inr (.inr j),h⟩ => False.elim (h (pool (.inr j) trivial))
  left_inv := by rintro (⟨v,⟨i,hi⟩⟩ | ⟨v,⟨i,hi⟩⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨v,i⟩ | ((j | j) | j),h⟩
    · rfl
    · obtain ⟨v,i⟩ := j; rfl
    · exact False.elim (h (pool (.inl (.inr j)) trivial))
    · exact False.elim (h (pool (.inr j) trivial))

theorem Spec.card_free_of_pool_covered (M : P.graph.Subgraph)
    (pool : ∀ t : P.Token, P.inPool t → (.inr t : P.Vertex) ∈ M.verts) :
    Nat.card {x : P.Vertex // x ∉ M.verts} =
      ∑ v, (Nat.card (P.FreeMust M v) + Nat.card (P.FreeSlot M v)) := by
  classical
  have eq := (Nat.card_congr (P.freeEquiv M pool)).symm
  simpa only [Nat.card_sum, Nat.card_sigma, Finset.sum_add_distrib] using eq

/-- Complement of an embedded family counts available positions not used by any pair. -/
theorem card_outside {I X : Type*} [Finite I] [Finite X] (e : I ↪ X) :
    Nat.card {x : X // x ∉ Set.range e} = Nat.card X - Nat.card I := by
  classical
  let := Fintype.ofFinite I
  let := Fintype.ofFinite X
  simp only [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, Fintype.card_range]

/-- For the available slots of an actual red graph, the two complementary
    ranges in the greedy construction have *exactly* the sum of its cap excesses. -/
theorem Spec.greedy_leftovers (F : SimpleGraph V) (hF : F ≤ P.G) (v : V)
    (cap : P.G.degree v ≤ P.A v + P.B v)
    (p : GreedyIndex (P.Available F v) (P.mandatoryCount v) (P.optionalCount v)) :
    Nat.card {i : Fin (P.mandatoryCount v) // i ∉ Set.range p.mandatoryToken} +
      Nat.card {s : P.Available F v // s ∉ Set.range p.allSlots} =
        (Nat.card (F.neighborSet v) - P.A v) +
          (P.G.degree v - Nat.card (F.neighborSet v) - P.B v) := by
  classical
  have redBound : Nat.card (F.neighborSet v) ≤ P.G.degree v := by
    let f (w : F.neighborSet v) : P.G.neighborSet v := ⟨w.val,hF w.property⟩
    have inj : Function.Injective f := by intro a b e; exact Subtype.ext (congrArg (fun w : P.G.neighborSet v => w.val) e)
    have b := Nat.card_le_card_of_injective f inj
    rwa [Nat.card_eq_fintype_card (α := P.G.neighborSet v), P.G.card_neighborSet_eq_degree] at b
  rw [card_outside, card_outside, Nat.card_fin, Nat.card_fin, GreedyIndex.pairCount,
      P.card_available F hF v]
  unfold Spec.mandatoryCount Spec.optionalCount Spec.padding
  omega

#print axioms Spec.greedy_leftovers

#print axioms Spec.card_free_of_pool_covered

end JSP452Audit.Padded
