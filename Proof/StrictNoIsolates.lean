import GlobalStrictFamily
import RowDelete

namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Both positive target windows survive removal of an isolated host vertex.
The row number and the two complete suffixes are unchanged. -/
theorem forcingRow_delete_isolate {X : Type*} (G : SimpleGraph X) (v : X)
    (isolated : ∀ w, ¬ G.Adj v w) {s t r : ℕ} (n m : ℕ → ℕ)
    (pn : ∀ i, i<s → 0<n i) (pm : ∀ j, j<t → 0<m j) (row : ForcingRow G s t n m r) :
    ForcingRow (G.induce {x | x ≠ v}) s t n m r := by
  intro i j l q hr hl hq lp qp R sub
  have posR (a : Fin l) : 1 ≤ n (i+a.val) := pn _ (by have := a.isLt; omega)
  have posB (b : Fin q) : 1 ≤ m (j+b.val) := pm _ (by have := b.isLt; omega)
  let A := restoreIncidentRed G v R
  have included : A ≤ G := restoreIncidentRed_le G v R
  rcases row i j l q hr hl hq lp qp A included with red | blue
  · have noEdge (w : X) : ¬ A.Adj v w := fun h => isolated w (included h)
    have keep := copy_avoids_isolated v (forest_has_neighbor _ posR) noEdge red
    rw [restoreIncidentRed_induce G v R sub] at keep
    exact Or.inl keep
  · have noEdge (w : X) : ¬ (G \ A).Adj v w := fun h => isolated w h.1
    have keep := copy_avoids_isolated v (forest_has_neighbor _ posB) noEdge blue
    rw [restoreIncidentRed_blue_induce G v R] at keep
    exact Or.inr keep

/-- Minimizing the host order among competitors of the same rank and edge
count rules out every isolated vertex in the strict family. -/
theorem minimal_strict_no_isolates (F : StrictFamily.{u})
    (minOrder : ∀ B : StrictFamily.{u}, B.rank = F.rank → B.edges = F.edges → F.order ≤ B.order)
    (v : F.X) : 0 < Nat.card (F.G.neighborSet v) := by
  by_contra! zero
  have isolated (w : F.X) : ¬ F.G.Adj v w := by
    intro edge
    have pos := (Set.ncard_pos (F.G.neighborSet v).toFinite).mpr ⟨w,edge⟩
    exact (Nat.not_lt_of_ge zero) pos
  let H := F.G.induce {x | x ≠ v}
  have eq : H.edgeSet.ncard = F.G.edgeSet.ncard := by
    have split := card_neighbor_add_induce_edge_ncard F.G v
    change Nat.card (F.G.neighborSet v) + H.edgeSet.ncard = F.G.edgeSet.ncard at split
    omega
  let B : StrictFamily.{u} := {
    F with X := {x : F.X // x ≠ v}, finiteX := inferInstance, G := H
           row := forcingRow_delete_isolate F.G v isolated _ _
             (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
           strict := eq.trans_lt F.strict }
  have order := minOrder B rfl eq
  have proper : ({x : F.X | x ≠ v} : Set F.X) ⊂ Set.univ :=
    ⟨Set.subset_univ _,fun back => (back (Set.mem_univ v)) rfl⟩
  have less := Set.ncard_lt_ncard proper
  rw [Set.ncard_univ] at less
  exact (Nat.not_lt_of_ge order) less

#print axioms forcingRow_delete_isolate
#print axioms minimal_strict_no_isolates
end JSP452Audit.StarHost
