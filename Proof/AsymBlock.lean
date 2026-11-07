import BlockColor

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Vertex-disjoint stars each have at least one leaf; one-leaf components count. -/
def PosCapacity {X : Type*} (C : SimpleGraph X) (p : ℕ) : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 1 ≤ n i) → (forest n).IsContained C → k ≤ p

/-- Color all edges meeting the chosen control set red. Under p ≤ q+1 the
remaining blue vertices number at most 3q+2, including the sharp boundary.
A singleton, empty host, or overlarge control budget also works. -/
theorem asym_block_color {X : Type*} [Finite X] (G : SimpleGraph X) (p q : ℕ)
    (size : Nat.card X ≤ 2 * (p+q) + 1) (order : p ≤ q+1) :
    ∃ R ≤ G, PosCapacity R p ∧ BlockCapacity (G \ R) q := by
  classical
  let _ := Fintype.ofFinite X
  have fits : min p (Fintype.card X) ≤ (Finset.univ : Finset X).card := by simp
  obtain ⟨B,_,count⟩ := Finset.exists_subset_card_eq fits
  let R : SimpleGraph X := G ⊓ fromRel (fun x y => x ∈ B ∨ y ∈ B)
  refine ⟨R, inf_le_left, ?_, ?_⟩
  · intro k n positive copy
    have cover : ∀ ⦃x y⦄, R.Adj x y → x ∈ B ∨ y ∈ B := by
      intro x y h
      exact h.2.2.elim id Or.symm
    exact (one_per_star_of_cover B cover positive copy).trans (count.le.trans (min_le_left _ _))
  · intro k n wide copy
    have support : ∀ ⦃x y⦄, (G \ R).Adj x y → x ∈ Bᶜ := by
      intro x y h
      exact Finset.mem_compl.mpr (fun hx => h.2 ⟨h.1,h.1.ne,Or.inl (Or.inl hx)⟩)
    have used := three_per_star_of_support Bᶜ support wide copy
    rw [Finset.card_compl, count] at used
    rw [Nat.card_eq_fintype_card] at size
    omega

#print axioms asym_block_color
end JSP452Audit.StarHost
