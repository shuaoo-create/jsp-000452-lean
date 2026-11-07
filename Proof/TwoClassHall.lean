import HallNeighborhoods
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fintype.Sum

namespace JSP452Audit.StarHost

/-- Hall allocation with d dummy seats, of which only the first k can be
assigned to full components. Every real-root seat respects the given relation. -/
theorem two_class_hall {A C : Type*} [Finite A] [Finite C] (L : A → C → Prop) (F : Set C)
    (d k : ℕ) (small : k ≤ d) (balance : Nat.card C = Nat.card A + d)
    (all : ∀ T : Set C, T.ncard ≤ (rootNeighbors L T).ncard + d)
    (full : ∀ T : Set C, T ⊆ F → T.ncard ≤ (rootNeighbors L T).ncard + k) :
    ∃ e : C ≃ (A ⊕ Fin d),
      (∀ c a, e c = .inl a → L a c) ∧
      (∀ c i, c ∈ F → e c = .inr i → i.val < k) := by
  classical
  let _ := Fintype.ofFinite A
  let _ := Fintype.ofFinite C
  let legal (c : C) : A ⊕ Fin d → Prop := Sum.elim (fun a => L a c) (fun i => c ∉ F ∨ i.val < k)
  let nbr (c : C) := Finset.univ.filter (legal c)
  have count (T : Finset C) (c : C) (hc : c ∈ T) (b : ℕ) (bd : b ≤ d)
      (can : ∀ i : Fin b, c ∉ F ∨ i.val < k) :
      (rootNeighbors L (T : Set C)).ncard + b ≤ (T.biUnion nbr).card := by
    let N := rootNeighbors L (T : Set C)
    let large (i : Fin b) : Fin d := ⟨i.val,lt_of_lt_of_le i.isLt bd⟩
    have left (a : ↥N) : (Sum.inl a.val : A ⊕ Fin d) ∈ T.biUnion nbr := by
      obtain ⟨j,hj,inc⟩ := a.property
      exact Finset.mem_biUnion.mpr ⟨j,hj,Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩⟩
    have right (i : Fin b) : (Sum.inr (large i) : A ⊕ Fin d) ∈ T.biUnion nbr :=
      Finset.mem_biUnion.mpr ⟨c,hc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,can i⟩⟩
    let f : ↥N ⊕ Fin b → ↥(T.biUnion nbr) :=
      Sum.elim (fun a => ⟨.inl a.val,left a⟩) (fun i => ⟨.inr (large i),right i⟩)
    have inj : Function.Injective f := by
      rintro (a | i) (z | j) eq
      · exact congrArg Sum.inl (Subtype.ext (Sum.inl.inj (congrArg Subtype.val eq)))
      · have e₀ : (Sum.inl a.val : A ⊕ Fin d) = .inr (large j) := congrArg Subtype.val eq
        cases e₀
      · have e₀ : (Sum.inr (large i) : A ⊕ Fin d) = .inl z.val := congrArg Subtype.val eq
        cases e₀
      · have same : large i = large j := Sum.inr.inj (congrArg Subtype.val eq)
        exact congrArg Sum.inr (Fin.ext (congrArg (fun z : Fin d => z.val) same))
    have cmp := Nat.card_le_card_of_injective f inj
    rw [Nat.card_sum,Nat.card_fin,Nat.card_eq_fintype_card (α := ↥(T.biUnion nbr)),Fintype.card_coe] at cmp
    exact cmp
  have hall (T : Finset C) : T.card ≤ (T.biUnion nbr).card := by
    by_cases nonempty : T.Nonempty
    · by_cases inside : (T : Set C) ⊆ F
      · obtain ⟨c,hc⟩ := nonempty
        have enough := full T inside
        rw [Set.ncard_coe_finset] at enough
        exact enough.trans (count T c hc k small (fun i => Or.inr i.isLt))
      · obtain ⟨c,hc,out⟩ := Set.not_subset.mp inside
        have enough := all T
        rw [Set.ncard_coe_finset] at enough
        exact enough.trans (count T c hc d le_rfl (fun _ => Or.inl out))
    · rw [Finset.not_nonempty_iff_eq_empty.mp nonempty]
      simp
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' nbr).mp hall
  have bij := (Nat.bijective_iff_injective_and_card f).mpr ⟨inj,by simpa only [Nat.card_sum,Nat.card_fin] using balance⟩
  let e := Equiv.ofBijective f bij
  have gets (c : C) : legal c (e c) := (Finset.mem_filter.mp (mem c)).2
  refine ⟨e,?_,?_⟩
  · intro c a eq
    have valid := gets c
    rw [eq] at valid
    exact valid
  · intro c i inside eq
    have allowed : legal c (.inr i) := eq ▸ gets c
    exact allowed.resolve_left (fun no => no inside)

#print axioms two_class_hall
end JSP452Audit.StarHost
