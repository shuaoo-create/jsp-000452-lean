import KeepTheOldExteriorPortsWhenJoiningEachActualLayer
namespace JSP452Audit.StarHost.ScaledPortPlan
open SimpleGraph
universe u
variable {X:Type u} [Finite X] {G:SimpleGraph X} {D k c:ℕ} {K:DegreeRegion G D} (P:ScaledPortPlan K k c)

noncomputable abbrev degreeAt (t:Fin k) (x:X) := Nat.card {i:P.portLabels t // P.parent t i=x}

theorem degree_on_selected_roots (t:Fin k) (x:X) (inside:x∈K.roots) : P.degreeAt t x=P.layers.loadAt t x := by
  let A := {i:PortMatching.cores P.matching|P.layers.colour i=t ∧ (PortMatching.mates P.proper i).val.1=x}
  let image (v:{i:P.portLabels t // P.parent t i=x}) : ↥A :=
    match v with
    | ⟨.inl e,hit⟩ => ⟨e.val,e.property,hit⟩
    | ⟨.inr r,hit⟩ => (r.property ((show r.val.val=x from hit).symm ▸ inside)).elim
  let e : {i:P.portLabels t // P.parent t i=x} ≃ ↥A := {
    toFun := image
    invFun := fun v => ⟨.inl ⟨v.val,v.property.1⟩,v.property.2⟩
    right_inv := fun _ => rfl
    left_inv := by
      rintro ⟨(e|r),hit⟩
      · rfl
      · exact (r.property ((show r.val.val=x from hit).symm ▸ inside)).elim}
  exact Nat.card_congr e

theorem degree_on_old_root (t:Fin k) (x:X) (inside:x∈K.barrier) (outside:x∉K.roots) : P.degreeAt t x=1 := by
  apply Nat.card_eq_one_iff_exists.mpr
  refine ⟨⟨.inr ⟨⟨x,inside⟩,outside⟩,rfl⟩,?_⟩
  rintro ⟨(e|r),hit⟩
  · exact (outside (hit ▸ P.new_parents_inside t e)).elim
  · exact Subtype.ext (congrArg Sum.inr (Subtype.ext (Subtype.ext hit)))

theorem layer_root_degrees (t:Fin k) (x:X) (root:x∈K.barrier) :
    1≤P.degreeAt t x ∧ (Nat.card (G.neighborSet x)=D → P.degreeAt t x=1) := by
  by_cases use:x∈K.roots
  · rw [P.degree_on_selected_roots t x use]
    have bound := P.layers.load_required t x use
    exact ⟨bound.1,fun full => bound.2 (by simp only [rootScale,full,Nat.sub_self,Nat.mul_zero,Nat.add_zero])⟩
  · rw [P.degree_on_old_root t x root use];simp

theorem aggregate_root_degree (x:X) (root:x∈K.barrier) :
    (∑t:Fin k,P.degreeAt t x)≤k+c*(D-Nat.card (G.neighborSet x)) := by
  by_cases use:x∈K.roots
  · simp_rw [P.degree_on_selected_roots _ x use];exact P.layers.root_load_total x
  · simp_rw [P.degree_on_old_root _ x root use];simp

theorem aggregate_full_misses :
    (∑t:Fin k,({Q|Q∉Set.range (P.component t) ∧ allFullComponent G K.barrier D Q}:Set _).ncard)=
      ∑t:Fin k,((P.layers.assigned t)ᶜ:Set K.pieces).ncard := by
  apply Finset.sum_congr rfl
  intro t _;rw [P.free_full_cores_in_one_layer,Set.ncard_image_of_injective _ Subtype.val_injective]

#print axioms degree_on_selected_roots
#print axioms degree_on_old_root
#print axioms layer_root_degrees
#print axioms aggregate_root_degree
#print axioms aggregate_full_misses
end JSP452Audit.StarHost.ScaledPortPlan
