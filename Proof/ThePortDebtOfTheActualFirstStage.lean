import ActualExteriorLeavesOfTheTwoPortBoxes
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

/-- At the moment the two nine-degree stages are joined, the only internal
edges of their union are retained L ports. A shared root is allowed. -/
theorem first_stage_port_debt (cap : ∀x,Nat.card (G.neighborSet x)≤9)
    (I B : Set X) (inside : I⊆R.chosen) (ind : G.IsIndepSet I) (stage : CompleteDegreeStage R.erased 9 B) :
    let S := I∪B
    (G.induce S).edgeSet.ncard+R.portCount≤2 ∧
      G.edgeSet.ncard+(G.induce S).edgeSet.ncard=(G.induce Sᶜ).edgeSet.ncard+9*S.ncard := by
  classical
  intro S
  let label (i : Fin 2) := s((R.port i).tip,(R.port i).root)
  let possible (i : Fin 2) : Set (Sym2 X) := if R.essential i then ∅ else {label i}
  have num (i : Fin 2) : (possible i).ncard+R.portCharge i=1 := by
    by_cases h : R.essential i <;> simp [possible,portCharge,h]
  have selected (i : Fin 2) (no : ¬R.essential i) : label i∈possible 0∪possible 1 := by
    have mem : label i∈possible i := by simp [possible,no]
    fin_cases i;exact Or.inl mem;exact Or.inr mem
  have actual (y) (hy : y∈B) := R.full_exterior_keeps_every_neighbor cap (stage.2.1 y hy)
  have cross (x y : X) (hx : x∈I) (hy : y∈B) (e : G.Adj x y) :
      s(x,y)∈possible 0∪possible 1 := by
    have kept : R.erased.Adj x y := (show x∈R.erased.neighborSet y from (actual y hy).symm ▸ e.symm).symm
    have side (i : Fin 2) (xin : x∈R.box i) : s(x,y)∈possible 0∪possible 1 := by
      obtain ⟨xt,yr,no⟩ := R.erased_edge_at_box i xin kept
      rw [xt,yr];exact selected i no
    exact (inside hx).elim (side 0) (side 1)
  let send : Sym2 (↥S)→Sym2 X := Sym2.map Subtype.val
  have sub : send '' (G.induce S).edgeSet⊆possible 0∪possible 1 := by
    rintro _ ⟨z,mem,rfl⟩
    induction z using Sym2.inductionOn with
    | _ x y =>
      have edge : G.Adj x.val y.val := mem
      change s(x.val,y.val)∈possible 0∪possible 1
      rcases x.property with xi|xb <;> rcases y.property with yi|yb
      · exact (ind xi yi edge.ne edge).elim
      · exact cross _ _ xi yb edge
      · rw [Sym2.eq_swap];exact cross _ _ yi xb edge.symm
      · have kept : y.val∈R.erased.neighborSet x.val := by rw [actual x.val xb];exact edge
        exact (stage.1 xb yb edge.ne kept).elim
  have cnt := Set.ncard_le_ncard sub
  have inj : Function.Injective send := Sym2.map.injective Subtype.val_injective
  rw [Set.ncard_image_of_injective _ inj] at cnt
  have joint := Set.ncard_union_le (possible 0) (possible 1)
  have n0 := num 0
  have n1 := num 1
  have full (x) (hx : x∈S) : Nat.card (G.neighborSet x)=9 := by
    rcases hx with i|b
    · exact R.chosen_full cap (inside i)
    · rw [←actual x b];exact stage.2.1 x b
  have fee := root_deletion_cost G S
  rw [degree_sum_full G S 9 full] at fee
  exact ⟨by dsimp only [portCount];omega,fee⟩

#print axioms first_stage_port_debt
end JSP452Audit.StarHost.NinePortRegion
