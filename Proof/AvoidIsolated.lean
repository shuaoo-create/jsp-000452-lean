import StarHost
import Mathlib.Combinatorics.SimpleGraph.Copy

namespace JSP452Audit.StarHost
open SimpleGraph

/-- No vertex of a copy can land on an isolated point if every source
    vertex is incident with an edge. The source and host may be infinite. -/
theorem copy_avoids_isolated {U X : Type*} {A : SimpleGraph U} {C : SimpleGraph X}
    (v : X) (source : ∀ a, ∃ b, A.Adj a b) (isolated : ∀ x, ¬ C.Adj v x)
    (h : A.IsContained C) : A.IsContained (C.induce {x | x ≠ v}) := by
  obtain ⟨f⟩ := h
  have away (a : U) : f a ≠ v := by
    intro same
    obtain ⟨b, edge⟩ := source a
    have mapped : C.Adj (f a) (f b) := f.toHom.map_rel edge
    rw [same] at mapped
    exact isolated _ mapped
  let restricted : A →g C.induce {x | x ≠ v} :=
    ⟨fun a => ⟨f a, away a⟩, fun edge => f.toHom.map_rel edge⟩
  exact ⟨restricted.toCopy (fun _ _ eq => f.injective (congrArg Subtype.val eq))⟩

/-- A center has its first leaf, and a leaf has its own center. The statement
    is vacuous when the family has no components. -/
theorem forest_has_neighbor {I : Type*} (n : I → ℕ) (positive : ∀ i, 1 ≤ n i) :
    ∀ a, ∃ b, (forest n).Adj a b := by
  rintro ⟨i, j⟩
  by_cases centerCase : j = 0
  · subst j
    let first : Leaves n := ⟨i, ⟨0, positive i⟩⟩
    exact ⟨leaf n first, starEdge n first⟩
  · obtain ⟨k,rfl⟩ := Fin.exists_succ_eq.mpr centerCase
    exact ⟨center n i, (starEdge n ⟨i,k⟩).symm⟩

#print axioms copy_avoids_isolated
#print axioms forest_has_neighbor
end JSP452Audit.StarHost
