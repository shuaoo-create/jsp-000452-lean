import RestoreTwo
import Mathlib.Data.Finset.Powerset

namespace JSP452Audit.StarHost
open SimpleGraph

/-- This is the Tutte score plus the fixed total number of vertices.  Using
    this nonnegative form avoids truncating cuts with negative score. -/
noncomputable def retainedScore {X : Type*} (G : SimpleGraph X) (W : Finset X) : ℕ :=
  (G.induce (W : Set X)).oddComponents.ncard + W.card

/-- Choose a genuinely maximizing retained set with the most vertices among
    all maximizers. Adding *any* excluded vertex then strictly lowers score. -/
theorem extremal_retained {X : Type*} [Finite X] (G : SimpleGraph X) :
    ∃ W : Finset X, (∀ U, retainedScore G U ≤ retainedScore G W) ∧
      ∀ (x : X) (U : Finset X), x ∉ W → (∀ y, y ∈ U ↔ y=x ∨ y∈W) →
        retainedScore G U < retainedScore G W := by
  classical
  let _ := Fintype.ofFinite X
  obtain ⟨Z,_,top⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Finset X)) (retainedScore G) ⟨∅,Finset.mem_univ _⟩
  let best := (Finset.univ : Finset (Finset X)).filter (fun U => retainedScore G U = retainedScore G Z)
  have memBest (U : Finset X) : U ∈ best ↔ retainedScore G U=retainedScore G Z := by simp [best]
  obtain ⟨W,hW,large⟩ := Finset.exists_max_image best Finset.card ⟨Z,(memBest Z).mpr rfl⟩
  have eq := (memBest W).mp hW
  have maxW (U : Finset X) := (top U (Finset.mem_univ _)).trans_eq eq.symm
  refine ⟨W,maxW,?_⟩
  intro x U outside spec
  have add : U=insert x W := by ext y; exact (spec y).trans Finset.mem_insert.symm
  by_contra! h
  have same := le_antisymm (maxW U) h
  have bound := large U ((memBest U).mpr (same.trans eq))
  rw [add, Finset.card_insert_of_notMem outside] at bound
  omega

#print axioms extremal_retained
end JSP452Audit.StarHost
