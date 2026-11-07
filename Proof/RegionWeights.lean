import ActualRegionRanks
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*}
noncomputable def crossCount (G : SimpleGraph X) (U V : Set X) : ℕ :=
  Nat.card {p : (↥U × ↥V) // G.Adj p.1.val p.2.val}

noncomputable def originalDegreeSum [Finite X] (G : SimpleGraph X) (U : Set X) : ℕ := by
  classical exact ∑ v ∈ U.toFinite.toFinset, Nat.card (G.neighborSet v)

/-- Internal surplus is signed: low-density components can have negative weight. -/
noncomputable def edgeSurplus [Finite X] (H : SimpleGraph X) (D : ℕ) : ℤ :=
  (H.edgeSet.ncard : ℤ) - (D : ℤ)*(matchingEdges H : ℤ)

theorem crossCount_swap (G : SimpleGraph X) (U V : Set X) : crossCount G U V=crossCount G V U := by
  apply Nat.card_congr
  exact {toFun := fun p => ⟨(p.val.2,p.val.1),p.property.symm⟩,
         invFun := fun p => ⟨(p.val.2,p.val.1),p.property.symm⟩,
         left_inv := fun _ => rfl, right_inv := fun _ => rfl}

theorem crossCount_of_no_edges (G : SimpleGraph X) (U V : Set X)
    (sep : ∀ x∈U, ∀ y∈V, ¬G.Adj x y) : crossCount G U V=0 := by
  let _ : IsEmpty {p : (↥U × ↥V) // G.Adj p.1.val p.2.val} :=
    ⟨fun p => sep _ p.val.1.property _ p.val.2.property p.property⟩
  exact Nat.card_eq_zero.mpr (Or.inl inferInstance)
#print axioms crossCount_swap
end JSP452Audit.StarHost