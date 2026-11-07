import FormalConjecturesForMathlib.Combinatorics.SimpleGraph.SizeRamsey

namespace JSP452Audit.StarHost

open SimpleGraph

/-- An actual finite forcing host gives an upper bound for the frozen size-Ramsey number,
whose defining infimum only quantifies over hosts with vertices `Fin n`. -/
theorem sizeRamsey_le_of_host {X α β : Type*} [Finite X] [Fintype α] [Fintype β]
    (F : SimpleGraph X) (G : SimpleGraph α) (H : SimpleGraph β)
    (forces : ∀ R : SimpleGraph X, R ≤ F → G.IsContained R ∨ H.IsContained (F \ R)) :
    sizeRamsey G H ≤ F.edgeSet.ncard := by
  classical
  let := Fintype.ofFinite X
  let n := Fintype.card X
  let e : X ≃ Fin n := Fintype.equivFin X
  let K : SimpleGraph (Fin n) := F.comap e.symm
  have edgeCount : K.edgeSet.ncard = F.edgeSet.ncard :=
    Nat.card_congr (SimpleGraph.Iso.comap e.symm F).mapEdgeSet
  apply Nat.sInf_le
  refine ⟨n, K, edgeCount, ?_⟩
  intro S hS
  let R : SimpleGraph X := S.comap e
  have sub : R ≤ F := by
    intro x y hxy
    change S.Adj (e x) (e y) at hxy
    have h := hS hxy
    change F.Adj (e.symm (e x)) (e.symm (e y)) at h
    simpa only [Equiv.symm_apply_apply] using h
  rcases forces R sub with red | blue
  · exact Or.inl (red.trans (SimpleGraph.Iso.comap e S).isContained)
  · have pullBlue : F \ R = (K \ S).comap e := by
      ext x y
      change (F.Adj x y ∧ ¬ S.Adj (e x) (e y)) ↔
        (F.Adj (e.symm (e x)) (e.symm (e y)) ∧ ¬ S.Adj (e x) (e y))
      simp only [Equiv.symm_apply_apply]
    rw [pullBlue] at blue
    exact Or.inr (blue.trans (SimpleGraph.Iso.comap e (K \ S)).isContained)

#print axioms sizeRamsey_le_of_host

end JSP452Audit.StarHost
