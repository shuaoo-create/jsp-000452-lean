import AvoidIsolated
import WitnessPair
import ExposeRestrict

namespace JSP452Audit.StarHost
open SimpleGraph

/-- The copy uses only vertices that are incident with an actual original edge.
Consequently it can be lifted to the vertex subtype of G.support. -/
private theorem restrict_copy_to_support {X Z : Type*} (G C : SimpleGraph X) (A : SimpleGraph Z)
    (sub : C ≤ G) (positive : ∀ z, ∃ w, A.Adj z w) (copy : A.IsContained C) :
    A.IsContained (C.induce G.support) := by
  obtain ⟨f⟩ := copy
  have lands (z : Z) : f z ∈ G.support := by
    obtain ⟨w,edge⟩ := positive z
    exact (sub (f.toHom.map_adj edge)).mem_support_left
  let lift : A →g C.induce G.support := ⟨fun z => ⟨f z,lands z⟩,fun edge => f.toHom.map_adj edge⟩
  exact ⟨lift.toCopy (fun _ _ eq => f.injective (congrArg Subtype.val eq))⟩

/-- Every coloring of the support extends along the original-label inclusion.
Positive forest copies of either color restrict back to the same support. -/
theorem forces_on_support {X I J : Type*} (G : SimpleGraph X) (n : I → ℕ) (m : J → ℕ)
    (pn : ∀ i, 0 < n i) (pm : ∀ j, 0 < m j) (force : Forces G (forest n) (forest m)) :
    Forces (G.induce G.support) (forest n) (forest m) := by
  intro R sub
  let C := R.spanningCoe
  have original : C ≤ G := (map_monotone _ sub).trans (G.spanningCoe_induce_le _)
  rcases force C original with red | blue
  · left
    simpa only [C,induce_spanningCoe] using
      restrict_copy_to_support G C _ original (forest_has_neighbor n pn) red
  · right
    have copied := restrict_copy_to_support G (G \ C) _ sdiff_le (forest_has_neighbor m pm) blue
    have eq : (G \ C).induce G.support = (G.induce G.support) \ R := by
      ext x y
      change (G.Adj x.val y.val ∧ ¬C.Adj x.val y.val) ↔
        (G.Adj x.val y.val ∧ ¬R.Adj x y)
      have inside : C.Adj x.val y.val ↔ R.Adj x y :=
        show (R.map (Function.Embedding.subtype _)).Adj x.val y.val ↔ R.Adj x y from map_adj_apply
      rw [inside]
    rwa [eq] at copied

theorem support_host_edge_count {X : Type*} (G : SimpleGraph X) :
    (G.induce G.support).edgeSet.ncard = G.edgeSet.ncard := by
  let e := Function.Embedding.subtype (· ∈ G.support)
  have eq : (G.induce G.support).map e = G := G.spanningCoe_induce_support
  have card := congrArg (fun H : SimpleGraph X => H.edgeSet.ncard) eq
  rw [edgeSet_map,Set.ncard_image_of_injective _ e.sym2Map.injective] at card
  exact card

theorem isolate_free_support_host {X I J : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (n : I → ℕ) (m : J → ℕ) (pn : ∀ i, 0 < n i) (pm : ∀ j, 0 < m j)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (force : Forces G (forest n) (forest m)) :
    (G.induce G.support).edgeSet.ncard = G.edgeSet.ncard ∧
    (∀ x : G.support, 0 < Nat.card ((G.induce G.support).neighborSet x) ∧
      Nat.card ((G.induce G.support).neighborSet x) ≤ D) ∧
    Forces (G.induce G.support) (forest n) (forest m) := by
  refine ⟨support_host_edge_count G,?_,forces_on_support G n m pn pm force⟩
  intro x
  obtain ⟨w,edge⟩ := x.property
  let y : G.support := ⟨w,edge.mem_support_right⟩
  have used : Nonempty ((G.induce G.support).neighborSet x) := ⟨⟨y,edge⟩⟩
  exact ⟨Nat.card_pos,(induced_neighbor_count_le G G.support x).trans (cap x.val)⟩

universe u
theorem isolate_free_forcing_host {X : Type u} {I J : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ)
    (n : I → ℕ) (m : J → ℕ) (pn : ∀ i, 0 < n i) (pm : ∀ j, 0 < m j)
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (force : Forces G (forest n) (forest m)) :
    ∃ (Y : Type u) (_ : Finite Y) (H : SimpleGraph Y), H.edgeSet.ncard = G.edgeSet.ncard ∧
      (∀ y, 0 < Nat.card (H.neighborSet y) ∧ Nat.card (H.neighborSet y) ≤ D) ∧
      Forces H (forest n) (forest m) :=
  ⟨G.support,inferInstance,G.induce G.support,isolate_free_support_host G D n m pn pm cap force⟩

#print axioms forces_on_support
#print axioms support_host_edge_count
#print axioms isolate_free_forcing_host
end JSP452Audit.StarHost
