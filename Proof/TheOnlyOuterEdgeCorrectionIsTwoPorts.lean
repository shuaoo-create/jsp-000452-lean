import OriginalLabelsOfTheTwoCumulativeDeletions
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost.NinePortRegion
open SimpleGraph
universe u
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable def outer_copy (B : Set X) :
    (G.induce (R.outer B)).Copy (R.erased.induce Bᶜ) where
  toHom := {
    toFun := fun x => ⟨x.val,fun b => x.property (Or.inr b)⟩
    map_rel' := fun {x y} edge => (R.erased_edges_off_boxes (fun w => x.property (Or.inl w))
      (fun w => y.property (Or.inl w))).mpr edge }
  injective' := fun _ _ eq => Subtype.ext (congrArg (fun z : ↥(Bᶜ : Set X) => z.val) eq)

theorem outer_actual_edge_interval (B : Set X) :
    (G.induce (R.outer B)).edgeSet.ncard≤(R.erased.induce Bᶜ).edgeSet.ncard ∧
    (R.erased.induce Bᶜ).edgeSet.ncard≤(G.induce (R.outer B)).edgeSet.ncard+2 := by
  classical
  let Y := R.erased.induce Bᶜ
  let V := {v : ↥(Bᶜ : Set X) | v.val∈R.outer B}
  let A := eraseInternal Y V
  let edge (i : Fin 2) := s((R.port i).tip,(R.port i).root)
  let ports : Set (Sym2 X) := {edge 0,edge 1}
  have port (i : Fin 2) : edge i∈ports := by fin_cases i <;> simp [ports]
  have oriented {x y : X} (hx : x∈R.chosen) (adj : R.erased.Adj x y) : s(x,y)∈ports := by
    have one (i : Fin 2) (mem : x∈R.box i) : s(x,y)∈ports := by
      obtain ⟨rfl,rfl,_⟩ := R.erased_edge_at_box i mem adj
      exact port i
    exact hx.elim (one 0) (one 1)
  let send : Sym2 (↥(Bᶜ : Set X))→Sym2 X := Sym2.map Subtype.val
  have inj : Function.Injective send := Sym2.map.injective Subtype.val_injective
  have labels : send '' A.edgeSet⊆ports := by
    rintro _ ⟨z,hz,rfl⟩
    induction z using Sym2.inductionOn with
    | _ x y =>
      have e : A.Adj x y := hz
      change s(x.val,y.val)∈ports
      by_cases hx : x.val∈R.chosen
      · exact oriented hx e.1
      · have xin : x∈V := fun bad => bad.elim hx x.property
        have yin : y.val∈R.chosen := by
          by_contra no;exact e.2 ⟨xin,show y∈V from fun bad => bad.elim no y.property⟩
        rw [Sym2.eq_swap];exact oriented yin e.1.symm
  have bound := Set.ncard_le_ncard labels
  rw [Set.ncard_image_of_injective _ inj] at bound
  have small : ports.ncard≤2 := by
    have h := Set.ncard_insert_le (edge 0) {(edge 1)}
    simpa [ports] using h
  have ob : R.outer B⊆Bᶜ := fun _ o b => o (Or.inr b)
  let f := original_induced_subset_iso R.erased Bᶜ (R.outer B) ob
  have size : (Y.induce V).edgeSet.ncard=(R.erased.induce (R.outer B)).edgeSet.ncard := Nat.card_congr f.mapEdgeSet
  have same : R.erased.induce (R.outer B)=G.induce (R.outer B) := by
    ext x y
    exact R.erased_edges_off_boxes (fun w => x.property (Or.inl w)) (fun w => y.property (Or.inl w))
  rw [same] at size
  have cost := erase_internal_edge_count Y V
  change Y.edgeSet.ncard=A.edgeSet.ncard+(Y.induce V).edgeSet.ncard at cost
  change (G.induce (R.outer B)).edgeSet.ncard≤Y.edgeSet.ncard ∧ Y.edgeSet.ncard≤(G.induce (R.outer B)).edgeSet.ncard+2
  omega

theorem second_exterior_cut_cost (H : ThreeDegreeStages R.erased 7) :
    Disjoint H.midCut R.chosen ∧
    (G.induce (R.outer H.midCut)).edgeSet.ncard+8*H.middle.ncard≤
      (G.induce (R.outer H.upper)).edgeSet.ncard+2 := by
  have b := R.full_stage_off_boxes H.upper H.first
  have price := JSP452Audit.StarHost.degree_on_independent_full_set (R.erased.induce H.upperᶜ) H.middle 8 H.second.2.1 H.second.1
  rw [nested_deletion_edges R.erased H.upper H.middle] at price
  have first := (R.outer_actual_edge_interval H.upper).2
  have last := (R.outer_actual_edge_interval H.midCut).1
  change (R.erased.induce H.upperᶜ).edgeSet.ncard=(R.erased.induce H.midCutᶜ).edgeSet.ncard+8*H.middle.ncard at price
  refine ⟨?_,by omega⟩
  apply Set.disjoint_left.mpr
  rintro x (old|⟨v,mem,rfl⟩) xin
  · exact Set.disjoint_left.mp b old xin
  · have full := H.second.2.1 v mem
    have degree := induced_neighbor_count_le R.erased H.upperᶜ v
    have leaf := R.erased_core_degree v.val xin
    omega

#print axioms outer_copy
#print axioms outer_actual_edge_interval
#print axioms second_exterior_cut_cost
end JSP452Audit.StarHost.NinePortRegion
