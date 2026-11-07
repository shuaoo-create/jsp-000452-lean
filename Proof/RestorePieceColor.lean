import WitnessPair

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Recover the original red coloring by adjoining P. Every genuinely blue
edge belongs to the old blue graph or to Q. The pieces may overlap. -/
theorem restore_piece_color {X : Type*} (G Y P Q : SimpleGraph X) (hY : Y ≤ G) (hP : P ≤ G)
    (cover : G ≤ (Y ⊔ P) ⊔ Q) (R : SimpleGraph X) (incl : R ≤ Y) :
    R ⊔ P ≤ G ∧ G \ (R ⊔ P) ≤ (Y \ R) ⊔ Q := by
  refine ⟨sup_le (incl.trans hY) hP,?_⟩
  intro x y blue
  have hg : G.Adj x y := blue.1
  have notRed : ¬(R.Adj x y ∨ P.Adj x y) := blue.2
  rcases cover hg with (old | fixedRed) | extraBlue
  · exact Or.inl ⟨old,fun red => notRed (Or.inl red)⟩
  · exact (notRed (Or.inr fixedRed)).elim
  · exact Or.inr extraBlue

/-- The forced pair still gives a genuine copy after the restored blue class
is enlarged to the union of the residual blue graph and Q. -/
theorem restored_pair_outcome {X I J : Type*} (G Y P Q : SimpleGraph X)
    (hY : Y ≤ G) (hP : P ≤ G) (cover : G ≤ (Y ⊔ P) ⊔ Q)
    (n : I → ℕ) (m : J → ℕ) (forces : Forces G (forest n) (forest m))
    (R : SimpleGraph X) (incl : R ≤ Y) :
    (forest n).IsContained (R ⊔ P) ∨ (forest m).IsContained ((Y \ R) ⊔ Q) := by
  obtain ⟨redSub,blueSub⟩ := restore_piece_color G Y P Q hY hP cover R incl
  exact (forces (R ⊔ P) redSub).imp_right (fun h => h.mono_right blueSub)

/-- Split the union of a finite graph family at any subfamily of indices. -/
theorem sup_pieces_split {X I : Type*} [Fintype I] [DecidableEq I]
    (piece : I → SimpleGraph X) (T : Finset I) :
    Finset.univ.sup piece = T.sup piece ⊔ Tᶜ.sup piece := by
  rw [← Finset.sup_union]
  congr 1
  ext i
  simp

#print axioms restore_piece_color
#print axioms restored_pair_outcome
#print axioms sup_pieces_split
end JSP452Audit.StarHost
