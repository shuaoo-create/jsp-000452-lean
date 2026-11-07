import AvoidIsolated
import Mathlib.Data.Finset.Card

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Finite X]

/-- Capacity for arbitrary lists of disjoint stars with at least two leaves per star. -/
def BlockCapacity (C : SimpleGraph X) (p : ℕ) : Prop :=
  ∀ (k : ℕ) (n : Fin k → ℕ), (∀ i, 2 ≤ n i) → (forest n).IsContained C → k ≤ p

/-- Every represented star uses three distinct points in a set supporting the color. -/
theorem three_per_star_of_support {C : SimpleGraph X} (S : Finset X)
    (supported : ∀ ⦃x y⦄, C.Adj x y → x ∈ S) {k : ℕ}
    {n : Fin k → ℕ} (wide : ∀ i, 2 ≤ n i) (copy : (forest n).IsContained C) :
    3 * k ≤ S.card := by
  classical
  obtain ⟨f⟩ := copy
  let triple (a : Fin k × Fin 3) : Vertices n :=
    ⟨a.1, ⟨a.2.val, by have := wide a.1; have := a.2.isLt; omega⟩⟩
  have lands (a : Fin k × Fin 3) : f (triple a) ∈ S := by
    obtain ⟨b, adj⟩ := forest_has_neighbor n (fun i => Nat.le_trans (by decide) (wide i)) (triple a)
    exact supported (f.toHom.map_rel adj)
  let insert (a : Fin k × Fin 3) : ↥S := ⟨_,lands a⟩
  have inj : Function.Injective insert := by
    intro a b e
    have same : triple a = triple b := f.injective (congrArg Subtype.val e)
    exact Prod.ext (congrArg Sigma.fst same)
      (Fin.ext (congrArg (fun v : Vertices n => v.2.val) same))
  have h := Nat.card_le_card_of_injective insert inj
  simpa [Nat.card_eq_fintype_card, Nat.mul_comm] using h

/-- A point cover uses at least one distinct point per represented nontrivial star. -/
theorem one_per_star_of_cover {C : SimpleGraph X} (B : Finset X)
    (covered : ∀ ⦃x y⦄, C.Adj x y → x ∈ B ∨ y ∈ B) {k : ℕ}
    {n : Fin k → ℕ} (positive : ∀ i, 1 ≤ n i) (copy : (forest n).IsContained C) :
    k ≤ B.card := by
  classical
  obtain ⟨f⟩ := copy
  let first (i : Fin k) : Leaves n := ⟨i, ⟨0, positive i⟩⟩
  let pick (i : Fin k) : Vertices n :=
    if f (center n i) ∈ B then center n i else leaf n (first i)
  have owner (i : Fin k) : (pick i).1 = i := by
    dsimp [pick]
    split <;> rfl
  have lands (i : Fin k) : f (pick i) ∈ B := by
    dsimp [pick]
    split
    next yes => exact yes
    next no => exact (covered (f.toHom.map_rel (starEdge n (first i)))).resolve_left no
  let insert (i : Fin k) : ↥B := ⟨_, lands i⟩
  have inj : Function.Injective insert := by
    intro i j e
    have same : pick i = pick j := f.injective (congrArg Subtype.val e)
    exact (owner i).symm.trans ((congrArg Sigma.fst same).trans (owner j))
  have h := Nat.card_le_card_of_injective insert inj
  simpa [Nat.card_eq_fintype_card] using h

private def outsideControls (G : SimpleGraph X) (B : Finset X) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ x ∉ B ∧ y ∉ B
  symm := ⟨by rintro x y ⟨g,hx,hy⟩; exact ⟨g.symm,hy,hx⟩⟩
  loopless := ⟨fun _ e => e.1.ne rfl⟩

private theorem block_color_ordered (G : SimpleGraph X) (p q : ℕ) (order : q ≤ p)
    (size : Nat.card X ≤ 2 * (p+q) + 1) :
    ∃ R ≤ G, BlockCapacity R p ∧ BlockCapacity (G \ R) q := by
  classical
  let _ := Fintype.ofFinite X
  have ene : (min q (Fintype.card X)) ≤ (Finset.univ : Finset X).card := by simp
  obtain ⟨B, _, count⟩ := Finset.exists_subset_card_eq ene
  let R := outsideControls G B
  refine ⟨R, fun _ _ e => e.1, ?_, ?_⟩
  · intro k n wide copy
    have used := three_per_star_of_support (C := R) Bᶜ
      (by intro x y e; exact Finset.mem_compl.mpr e.2.1) wide copy
    rw [Finset.card_compl, count] at used
    rw [Nat.card_eq_fintype_card] at size
    omega
  · intro k n wide copy
    have covered : ∀ ⦃x y⦄, (G \ R).Adj x y → x ∈ B ∨ y ∈ B := by
      intro x y e
      by_contra! no
      exact e.2 ⟨e.1,no⟩
    have used := one_per_star_of_cover B covered (fun i => Nat.le_trans (by decide) (wide i)) copy
    omega

/-- Actual edge partition of a bounded-order block. Both capacities hold for
all star lists at once, including the empty list. No inhabitedness is required. -/
theorem block_color_capacity (G : SimpleGraph X) (p q : ℕ)
    (size : Nat.card X ≤ 2 * (p+q) + 1) :
    ∃ R ≤ G, BlockCapacity R p ∧ BlockCapacity (G \ R) q := by
  rcases le_total q p with h | h
  · exact block_color_ordered G p q h size
  · obtain ⟨B,hB,blue,red⟩ := block_color_ordered G q p h (by simpa [Nat.add_comm] using size)
    exact ⟨G \ B, sdiff_le, red, by simpa only [sdiff_sdiff_eq_self hB] using blue⟩

theorem block_color_excludes (G : SimpleGraph X) (p q : ℕ)
    (size : Nat.card X ≤ 2 * (p+q) + 1) :
    ∃ R ≤ G,
      (∀ n : Fin (p+1) → ℕ, (∀ i, 2 ≤ n i) → ¬ (forest n).IsContained R) ∧
      (∀ m : Fin (q+1) → ℕ, (∀ j, 2 ≤ m j) → ¬ (forest m).IsContained (G \ R)) := by
  obtain ⟨R,leG,red,blue⟩ := block_color_capacity G p q size
  exact ⟨R, leG, fun n wide copy => (Nat.not_succ_le_self p) (red _ n wide copy),
    fun m wide copy => (Nat.not_succ_le_self q) (blue _ m wide copy)⟩

#print axioms three_per_star_of_support
#print axioms one_per_star_of_cover
#print axioms block_color_capacity
#print axioms block_color_excludes
end JSP452Audit.StarHost
