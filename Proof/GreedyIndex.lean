import Mathlib.Data.Fintype.EquivFin
import Mathlib.SetTheory.Cardinal.Finite

namespace JSP452Audit

/-- A pair of indices for each edge of a local greedy allocation. Mandatory
tokens use the first available slots; optional tokens use only remaining slots. -/
structure GreedyIndex (S : Type*) (m o : ℕ) where
  mandatorySlot : Fin (min (Nat.card S) m) ↪ S
  mandatoryToken : Fin (min (Nat.card S) m) ↪ Fin m
  optionalSlot : Fin (min (Nat.card S - min (Nat.card S) m) o) ↪ S
  optionalToken : Fin (min (Nat.card S - min (Nat.card S) m) o) ↪ Fin o
  slots_ne : ∀ i j, mandatorySlot i ≠ optionalSlot j

/-- Put a block of `n` consecutive indices into an interval of size `size`. -/
private def intervalEmbedding (start n size : ℕ) (h : start + n ≤ size) : Fin n ↪ Fin size where
  toFun i := ⟨start + i.val, by have := i.isLt; omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    have he := congrArg Fin.val h
    exact Nat.add_left_cancel he

/-- The construction works also for empty slots or either empty token class. -/
noncomputable def greedyIndex (S : Type*) [Finite S] (m o : ℕ) : GreedyIndex S m o := by
  letI := Fintype.ofFinite S
  let enumerate : S ≃ Fin (Nat.card S) :=
    Fintype.equivFinOfCardEq (Nat.card_eq_fintype_card.symm)
  let k := min (Nat.card S) m
  let l := min (Nat.card S - k) o
  have hk : k ≤ Nat.card S := min_le_left _ _
  have hl : l ≤ Nat.card S - k := min_le_left _ _
  let first := intervalEmbedding 0 k (Nat.card S) (by omega)
  let second := intervalEmbedding k l (Nat.card S) (by omega)
  refine {
    mandatorySlot := first.trans enumerate.symm.toEmbedding
    mandatoryToken := intervalEmbedding 0 k m (by simpa only [Nat.zero_add] using min_le_right (Nat.card S) m)
    optionalSlot := second.trans enumerate.symm.toEmbedding
    optionalToken := intervalEmbedding 0 l o (by simpa only [Nat.zero_add] using min_le_right (Nat.card S - k) o)
    slots_ne := ?_ }
  intro i j same
  have he : first i = second j := enumerate.symm.injective same
  have hv := congrArg Fin.val he
  change 0 + i.val = k + j.val at hv
  have hi : i.val < k := i.isLt
  omega

namespace GreedyIndex

/-- The mandatory and optional slot images are disjoint as actual subsets of S. -/
theorem slotRanges_disjoint {S : Type*} {m o : ℕ} (p : GreedyIndex S m o) :
    Disjoint (Set.range p.mandatorySlot) (Set.range p.optionalSlot) := by
  rw [Set.disjoint_left]
  rintro _ ⟨i, rfl⟩ ⟨j, h⟩
  exact p.slots_ne i j h.symm

/-- Both batches of pairs use each slot at most once. -/
def allSlots {S : Type*} {m o : ℕ} (p : GreedyIndex S m o) :
    Fin (min (Nat.card S) m) ⊕ Fin (min (Nat.card S - min (Nat.card S) m) o) ↪ S where
  toFun := Sum.elim p.mandatorySlot p.optionalSlot
  inj' := by
    intro a b h
    obtain a | a := a <;> obtain b | b := b
    · exact congrArg Sum.inl (p.mandatorySlot.injective h)
    · exact (p.slots_ne a b h).elim
    · exact (p.slots_ne b a h.symm).elim
    · exact congrArg Sum.inr (p.optionalSlot.injective h)

/-- Total number of pairs, with no assumption on which side runs out first. -/
theorem pairCount (S : Type*) (m o : ℕ) :
    Nat.card (Fin (min (Nat.card S) m) ⊕
      Fin (min (Nat.card S - min (Nat.card S) m) o)) = min (Nat.card S) (m + o) := by
  rw [Nat.card_sum, Nat.card_fin, Nat.card_fin]
  omega

end GreedyIndex

#print axioms greedyIndex
#print axioms GreedyIndex.slotRanges_disjoint
#print axioms GreedyIndex.allSlots
#print axioms GreedyIndex.pairCount
end JSP452Audit
