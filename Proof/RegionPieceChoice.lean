import HeavyPieceSelection
import PositiveRootDebt

namespace JSP452Audit.StarHost.DegreeRegion
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} {D : ℕ} (K : DegreeRegion G D)

/-- Matching capacity of one actual positive component of the degree region. -/
noncomputable def pieceCapacity (c : ↥K.positive) : ℕ :=
  matchingEdges ((G.induce K.barrierᶜ).induce c.val.supp)

/-- Signed edge surplus of the same positive component. -/
noncomputable def pieceWeight (c : ↥K.positive) : ℤ :=
  edgeSurplus ((G.induce K.barrierᶜ).induce c.val.supp) D

theorem piece_weight_sum [Fintype ↥K.positive] :
    edgeSurplus (G.induce K.positiveCore) D = ∑ c : ↥K.positive, K.pieceWeight c :=
  core_surplus_eq_sum G K.barrier K.positive D

theorem positive_piece_bounds (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (c : ↥K.positive) :
    0 < K.pieceWeight c ∧ K.pieceWeight c ≤ (↑(D/2) : ℤ) ∧
    K.pieceWeight c ≤ (K.pieceCapacity c : ℤ) ∧ 0 < K.pieceCapacity c := by
  let Q := (G.induce K.barrierᶜ).induce c.val.supp
  let _ : Nonempty c.val.supp := c.val.nonempty_supp.to_subtype
  have restricted (x : c.val.supp) : Nat.card (Q.neighborSet x) ≤ D :=
    (induced_neighbor_count_le (G.induce K.barrierᶜ) c.val.supp x).trans
      ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap _))
  have positive : 0 < edgeSurplus Q D := c.property.2
  obtain ⟨_,double,rank⟩ := positive_core_caps Q (K.critical c.val).2 D restricted positive
  change 0 < edgeSurplus Q D ∧ edgeSurplus Q D ≤ (↑(D/2) : ℤ) ∧
    edgeSurplus Q D ≤ (matchingEdges Q : ℤ) ∧ 0 < matchingEdges Q
  exact ⟨positive,by omega,rank,by omega⟩

/-- Keep a concrete nonempty family of positive pieces with bounded weight
loss. The p+1 actual outside capacities dominate every retained capacity. -/
theorem choose_heavy_pieces [Fintype ↥K.positive] [DecidableEq ↥K.positive]
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D)
    (heavy : (↑(D/2) : ℤ)*(↑(D/2)+1) < edgeSurplus (G.induce K.positiveCore) D) :
    ∃ T : Finset ↥K.positive, T.Nonempty ∧ Tᶜ.card = D/2+1 ∧
      (∀ y ∈ Tᶜ, ∀ x ∈ T, K.pieceCapacity x ≤ K.pieceCapacity y) ∧
      edgeSurplus (G.induce K.positiveCore) D - (↑(D/2) : ℤ)*(↑(D/2)+1) ≤ ∑ x ∈ T, K.pieceWeight x ∧
      (∀ x ∈ T, 0 < K.pieceCapacity x) ∧ ∃ Z ∈ T, ∀ x ∈ T, K.pieceCapacity x ≤ K.pieceCapacity Z := by
  rw [K.piece_weight_sum] at heavy ⊢
  obtain ⟨T,nonempty,card,above,weight,largest⟩ := heavy_piece_selection K.pieceCapacity K.pieceWeight
    (D/2) (fun c => (K.positive_piece_bounds cap c).1) (fun c => (K.positive_piece_bounds cap c).2.1) heavy
  exact ⟨T,nonempty,card,above,weight,fun x _ => (K.positive_piece_bounds cap x).2.2.2,largest⟩

#print axioms piece_weight_sum
#print axioms positive_piece_bounds
#print axioms choose_heavy_pieces
end JSP452Audit.StarHost.DegreeRegion
