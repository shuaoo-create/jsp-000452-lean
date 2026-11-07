import TypedUniformWidthOnActualDeletion
namespace JSP452Audit.StarHost
open SimpleGraph

noncomputable def closedResidualIso {X:Type*} (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (A:Set U) (B:Set ↥(Uᶜ:Set X)) :
    ((G.induce U).induce Aᶜ ⊕g (G.induce Uᶜ).induce Bᶜ) ≃g G.induce (Subtype.val '' A∪Subtype.val '' B)ᶜ := by
  let S := Subtype.val '' A∪Subtype.val '' B
  let left (x:↥(Aᶜ:Set U)) : ↥(Sᶜ:Set X) := ⟨x.val.val,by
    rintro (⟨v,hv,eq⟩|⟨v,_,eq⟩)
    · exact x.property ((Subtype.ext eq : v=x.val) ▸ hv)
    · exact v.property (eq ▸ x.val.property)⟩
  let right (y:↥(Bᶜ:Set ↥(Uᶜ:Set X))) : ↥(Sᶜ:Set X) := ⟨y.val.val,by
    rintro (⟨v,_,eq⟩|⟨v,hv,eq⟩)
    · exact y.val.property (eq ▸ v.property)
    · exact y.property ((Subtype.ext eq : v=y.val) ▸ hv)⟩
  let send := Sum.elim left right
  have inj : Function.Injective send := by
    rintro (x|y) (w|z) eq
    · exact congrArg Sum.inl (Subtype.ext (Subtype.ext (congrArg (fun v:↥(Sᶜ:Set X) => v.val) eq)))
    · have same : x.val.val=z.val.val := congrArg Subtype.val eq
      exact (z.val.property (same ▸ x.val.property)).elim
    · have same : y.val.val=w.val.val := congrArg Subtype.val eq
      exact (y.val.property (same ▸ w.val.property)).elim
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext (congrArg (fun v:↥(Sᶜ:Set X) => v.val) eq)))
  have onto : Function.Surjective send := by
    intro v
    by_cases member:v.val∈U
    · let x:U := ⟨v.val,member⟩
      exact ⟨.inl ⟨x,fun hx => v.property (Or.inl ⟨x,hx,rfl⟩)⟩,rfl⟩
    · let y:↥(Uᶜ:Set X) := ⟨v.val,member⟩
      exact ⟨.inr ⟨y,fun hy => v.property (Or.inr ⟨y,hy,rfl⟩)⟩,rfl⟩
  refine ⟨Equiv.ofBijective send ⟨inj,onto⟩,?_⟩
  rintro (x|x) (y|y)
  · rfl
  · exact ⟨fun h => (y.val.property (closed _ x.val.property _ h)).elim,fun h => (not_adj_sum_inl_inr _ _ h).elim⟩
  · exact ⟨fun h => (x.val.property (closed _ y.val.property _ (show G.Adj x.val.val y.val.val from h).symm)).elim,fun h => (not_adj_sum_inl_inr _ _ h.symm).elim⟩
  · rfl

theorem exposure_after_closed_stage_split {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (A:Set U) (B:Set ↥(Uᶜ:Set X)) (D:ℕ) :
    minimumExposure (G.induce (Subtype.val '' A∪Subtype.val '' B)ᶜ) D=
      minimumExposure ((G.induce U).induce Aᶜ) D+minimumExposure ((G.induce Uᶜ).induce Bᶜ) D := by
  rw [←minimumExposure_iso (closedResidualIso G U closed A B) D,minimumExposure_sumGraph]

#print axioms exposure_after_closed_stage_split
end JSP452Audit.StarHost
