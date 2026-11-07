import OutsideSupply
import PositiveRootDebt
import WholeComponentPieces

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X] {G : SimpleGraph X} {D : ℕ}

/-- Choose b independent full-degree original labels from the unselected positive
components. No retained piece is incident to any chosen label. -/
theorem selected_outside_vertices (K : DegreeRegion G D) [Fintype ↥K.positive] [DecidableEq ↥K.positive]
    (T : Finset ↥K.positive) (Z b : ℕ) (many : Tᶜ.card = D/2+1)
    (rankFloor : ∀ c ∈ Tᶜ, Z ≤ matchingEdges ((G.induce K.barrierᶜ).induce c.val.supp))
    (cap : ∀ x, Nat.card (G.neighborSet x) ≤ D) (bMax : b ≤ Z+1) :
    ∃ U : Set X, U.ncard = b ∧ G.IsIndepSet U ∧
      (∀ x ∈ U, Nat.card (G.neighborSet x) = D) ∧
      ∀ c ∈ T, ∀ ⦃x y : X⦄, (wholePiece G K.barrier c.val).Adj x y → x ∉ U := by
  classical
  let outside : Set (G.induce K.barrierᶜ).ConnectedComponent :=
    Subtype.val '' (↑(Tᶜ) : Set ↥K.positive)
  let inside : Set (G.induce K.barrierᶜ).ConnectedComponent :=
    Subtype.val '' (T : Set ↥K.positive)
  have count : outside.ncard = D/2+1 := by
    dsimp only [outside]
    rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]
    exact many
  have order (c) (hc : c ∈ outside) : 2*Z+1 ≤ Nat.card c.supp := by
    obtain ⟨w,hw,rfl⟩ := hc
    obtain ⟨q,hq⟩ := w.val.nonempty_supp
    have actual := factorCritical_order_rank ((G.induce K.barrierᶜ).induce w.val.supp)
      (K.critical w.val).2 ⟨q,hq⟩
    have floor := rankFloor w hw
    omega
  have full : outside ⊆ {c | allFullComponent G K.barrier D c} := by
    rintro _ ⟨c,_,rfl⟩
    exact K.full c.property.1
  have dis : Disjoint inside outside := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨c,hc,rfl⟩ ⟨d,hd,eq⟩
    have same : d = c := Subtype.ext eq
    exact (Finset.mem_compl.mp hd) (same.symm ▸ hc)
  obtain ⟨U,sub,ind,card⟩ := outside_independent_supply G K.barrier outside D (D/2) Z b
    (by omega) count order cap bMax
  refine ⟨U,card,ind,fun x hx => regionCore_full_degree G K.barrier outside D full (sub hx),?_⟩
  intro c hc x y edge hx
  obtain ⟨z,hz,rfl⟩ := ((wholePiece_adj G K.barrier c.val x y).mp edge).2.1
  have included : (G.induce K.barrierᶜ).connectedComponentMk z ∈ inside :=
    ⟨c,hc,(show (G.induce K.barrierᶜ).connectedComponentMk z = c.val from hz).symm⟩
  have region : z.val ∈ regionCore G K.barrier inside := ⟨z,rfl,included⟩
  exact Set.disjoint_left.mp (disjoint_regionCore_indices G K.barrier dis) region (sub hx)

#print axioms selected_outside_vertices
end JSP452Audit.StarHost
