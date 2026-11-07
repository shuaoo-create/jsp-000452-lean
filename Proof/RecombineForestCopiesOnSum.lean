import StrictExteriorParityAndStages
namespace JSP452Audit.StarHost
open SimpleGraph

theorem recombine_forest_copies {I X Y : Type*} (G : SimpleGraph X) (H : SimpleGraph Y)
    (n : I→ℕ) (U : Set I)
    (left : (forest (fun i:U => n i.val)).IsContained G)
    (right : (forest (fun i:↥(Uᶜ : Set I) => n i.val)).IsContained H) :
    (forest n).IsContained (G ⊕g H) := by
  classical
  obtain ⟨L⟩ := left
  obtain ⟨R⟩ := right
  let tag (v:Vertices n) : Vertices (fun i:U => n i.val) ⊕ Vertices (fun i:↥(Uᶜ : Set I) => n i.val) :=
    if hv:v.1∈U then Sum.inl ⟨⟨v.1,hv⟩,v.2⟩ else Sum.inr ⟨⟨v.1,hv⟩,v.2⟩
  let forget : Vertices (fun i:U => n i.val) ⊕ Vertices (fun i:↥(Uᶜ : Set I) => n i.val) → Vertices n :=
    Sum.elim (fun v => ⟨v.1.val,v.2⟩) (fun v => ⟨v.1.val,v.2⟩)
  have inv (v:Vertices n) : forget (tag v)=v := by
    rcases v with ⟨i,z⟩
    by_cases h:i∈U <;> simp [forget,tag,h]
  let send := (Sum.map L R) ∘ tag
  have inj : Function.Injective send := (Sum.map_injective.mpr ⟨L.injective,R.injective⟩).comp (Function.LeftInverse.injective inv)
  refine ⟨{ toHom := {toFun := send,map_rel' := ?_},injective' := inj }⟩
  intro x y adj
  let e : (forest n).edgeSet := ⟨s(x,y),(forest n).mem_edgeSet.mpr adj⟩
  obtain ⟨⟨i,j⟩,eq⟩ := (edgeEquiv n).surjective e
  have ends : s(center n i,leaf n ⟨i,j⟩)=s(x,y) := congrArg Subtype.val eq
  have step : (G ⊕g H).Adj (send (center n i)) (send (leaf n ⟨i,j⟩)) := by
    by_cases h:i∈U
    · simpa [send,tag,center,leaf,h] using L.toHom.map_rel' (starEdge (fun z:U => n z.val) ⟨⟨i,h⟩,j⟩)
    · simpa [send,tag,center,leaf,h] using R.toHom.map_rel' (starEdge (fun z:↥(Uᶜ : Set I) => n z.val) ⟨⟨i,h⟩,j⟩)
  rcases Sym2.eq_iff.mp ends with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact step
  · exact step.symm

#print axioms recombine_forest_copies
end JSP452Audit.StarHost
