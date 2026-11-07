import WitnessPair
import EdgeBudgetLower

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The center of a genuine copy has at least the required number of distinct neighbors. -/
theorem high_degree_of_star {X : Type*} [Finite X] {C : SimpleGraph X} {a : ℕ}
    (h : (oneStar a).IsContained C) :
    ∃ v : X, a ≤ Nat.card (C.neighborSet v) := by
  obtain ⟨f⟩ := h
  let n := fun _ : Fin 1 => a
  let v := f (center n 0)
  let injectLeaf (l : Fin a) : C.neighborSet v :=
    ⟨f (leaf n ⟨0,l⟩),f.toHom.map_adj (starEdge n ⟨0,l⟩)⟩
  have inj : Function.Injective injectLeaf := by
    intro i j h
    have verts := f.injective (congrArg (fun w : C.neighborSet v => w.val) h)
    have vals := congrArg (fun z : Vertices n => z.2.val) verts
    exact Fin.ext (Nat.succ.inj vals)
  exact ⟨v,by simpa only [Nat.card_fin] using Nat.card_le_card_of_injective injectLeaf inj⟩

theorem positive_star_not_in_bot {X : Type*} {a : ℕ} (ha : 0<a) :
    ¬(oneStar a).IsContained (⊥ : SimpleGraph X) := by
  rintro ⟨f⟩
  exact f.toHom.map_adj (starEdge (fun _ : Fin 1 => a) ⟨0,⟨0,ha⟩⟩)

/-- Choose a monochrome coloring to exhibit the required high-degree vertex
    in the actual host, rather than in an auxiliary colored graph. -/
theorem high_degree_of_blue {X : Type*} [Finite X] (G : SimpleGraph X) {a b : ℕ}
    (ha : 0<a) (h : Forces G (oneStar a) (oneStar b)) :
    ∃ v : X, b ≤ Nat.card (G.neighborSet v) := by
  rcases h ⊥ bot_le with red | blue
  · exact (positive_star_not_in_bot ha red).elim
  · apply high_degree_of_star
    simpa using blue

/-- Only positive finite-list demands occur on the legal row. -/
theorem select_blue_center {X : Type*} [Finite X] {s t r : ℕ} (G : SimpleGraph X)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (pn : ∀ i, 1 ≤ n i)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i : Fin s) (j : Fin t) (sum : i.val+j.val=r) :
    ∃ v : X, m j ≤ Nat.card (G.neighborSet v) := by
  have forced := row_forces_star_pair G _ _ row i j sum
  have ni : padDemand n i.val = n i := dif_pos i.isLt
  have mj : padDemand m j.val = m j := dif_pos j.isLt
  rw [ni,mj] at forced
  exact high_degree_of_blue G (pn i) forced

#print axioms high_degree_of_star
#print axioms select_blue_center
end JSP452Audit.StarHost
