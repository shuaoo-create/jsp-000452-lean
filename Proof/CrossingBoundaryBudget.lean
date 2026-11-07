import TightCliqueFamily
namespace JSP452Audit.StarHost
open SimpleGraph

theorem sum_cross_into_disjoint {X J : Type*} [Finite X] [Fintype J]
    (G : SimpleGraph X) (A T : Set X) (C : J → Set X)
    (inside : ∀ i, C i ⊆ T) (apart : ∀ i j, i ≠ j → Disjoint (C i) (C j)) :
    (∑ i, crossCount G A (C i)) ≤ crossCount G A T := by
  classical
  let _ := Fintype.ofFinite A
  simp only [crossCount_eq_neighbor_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro x _
  let S (i : J) := G.neighborSet x.val ∩ C i
  have dis : Pairwise (Function.onFun Disjoint S) := by
    intro i j ne
    exact (apart i j ne).mono Set.inter_subset_right Set.inter_subset_right
  have sub : (⋃ i, S i) ⊆ G.neighborSet x.val ∩ T := by
    intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hy
    exact ⟨hi.1, inside i hi.2⟩
  have bound := Set.ncard_le_ncard sub
  rw [Set.ncard_iUnion_of_finite (fun i => Set.toFinite (S i)) dis,
    finsum_eq_sum_of_fintype] at bound
  exact bound

private theorem split_cross_to_two {X : Type*} [Finite X] (G : SimpleGraph X)
    (A V R S : Set X)
    (cover : ∀ a ∈ A, ∀ b ∈ V, G.Adj a b → b ∈ R ∨ b ∈ S) :
    crossCount G A V ≤ crossCount G A R + crossCount G A S := by
  classical
  let _ := Fintype.ofFinite A
  simp only [crossCount_eq_neighbor_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro a _
  have sub : G.neighborSet a.val ∩ V ⊆
      (G.neighborSet a.val ∩ R) ∪ (G.neighborSet a.val ∩ S) := by
    intro b hb
    rcases cover a.val a.property b hb.2 hb.1 with h | h
    · exact Or.inl ⟨hb.1, h⟩
    · exact Or.inr ⟨hb.1, h⟩
  exact (Set.ncard_le_ncard sub).trans (Set.ncard_union_le _ _)

/-- Boundary edges reaching the roots cost at most their total degree.
The remaining edges may be counted at both the preferred and ordinary ends. -/
theorem preferred_cut_corrected_budget {X J : Type*} [Finite X] [Fintype J]
    (G : SimpleGraph X) (C : J → Set X) (p : J) (I : Set X) (D : ℕ)
    (apart : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (outside : ∀ i, C i ⊆ Iᶜ)
    (ordinary : ∀ i, i ≠ p → ∀ a ∈ C i, ∀ b, G.Adj a b → b ∉ C i → b ∈ I ∨ b ∈ C p)
    (cap : ∀ x ∈ I, Nat.card (G.neighborSet x) ≤ D) :
    (∑ i, crossCount G (C i) (C i)ᶜ) ≤ I.ncard * D +
      2 * crossCount G (C p) ((C p)ᶜ ∩ Iᶜ) := by
  classical
  let O : Set X := (C p)ᶜ ∩ Iᶜ
  let F (i : J) : Set X := if i = p then ∅ else C i
  let e := crossCount G (C p) O
  have subsetF (i : J) : F i ⊆ C i := by
    by_cases h : i = p <;> simp [F,h]
  have insideF (i : J) : F i ⊆ O := by
    by_cases h : i = p
    · simp [F,h]
    · intro y hy
      have hc := subsetF i hy
      exact ⟨fun hp => Set.disjoint_left.mp (apart i p h) hc hp, outside i hc⟩
  have each (i : J) : crossCount G (C i) (C i)ᶜ ≤
      crossCount G I (C i) + crossCount G (C p) (F i) + (if i = p then e else 0) := by
    by_cases h : i = p
    · subst i
      have bound := split_cross_to_two G (C p) (C p)ᶜ I O (by
        intro a ha b hb edge
        by_cases hi : b ∈ I
        · exact Or.inl hi
        · exact Or.inr ⟨hb, hi⟩)
      have empt : crossCount G (C p) ∅ = 0 := crossCount_of_no_edges G (C p) ∅ (by simp)
      rw [crossCount_swap G (C p) I] at bound
      simpa [F, e, empt] using bound
    · have bound := split_cross_to_two G (C i) (C i)ᶜ I (C p)
          (fun a ha b hb edge => ordinary i h a ha b edge hb)
      rw [crossCount_swap G (C i) I, crossCount_swap G (C i) (C p)] at bound
      simpa [F, h] using bound
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun i _ => each i)
  simp only [Finset.sum_add_distrib] at summed
  have spike : (∑ i : J, if i = p then e else 0) = e := by simp
  rw [spike] at summed
  have spill := sum_cross_into_disjoint G (C p) O F insideF
    (fun i j ne => (apart i j ne).mono (subsetF i) (subsetF j))
  have roots := sum_cross_into_disjoint G I Set.univ C
    (fun i => Set.subset_univ _) apart
  let _ := Fintype.ofFinite I
  have rootCap : crossCount G I Set.univ ≤ I.ncard * D := by
    rw [crossCount_eq_neighbor_sum]
    calc
      _ ≤ ∑ _ : I, D := Finset.sum_le_sum (fun x _ => by
        rw [Set.inter_univ, ← Nat.card_coe_set_eq]
        exact cap x.val x.property)
      _ = _ := by simp [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]
  have paid := roots.trans rootCap
  change (∑ i, crossCount G (C i) (C i)ᶜ) ≤ I.ncard * D + 2 * e
  change (∑ i, crossCount G (C p) (F i)) ≤ e at spill
  omega

#print axioms preferred_cut_corrected_budget
end JSP452Audit.StarHost
