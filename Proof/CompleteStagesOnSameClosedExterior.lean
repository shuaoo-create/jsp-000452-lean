import SixStagePaidFiveWidth
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem closed_set_degree_eq {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (x:U) :
    Nat.card ((G.induce U).neighborSet x)=Nat.card (G.neighborSet x.val) := by
  have sub : G.neighborSet x.val⊆U := fun y edge => closed x.val x.property y edge
  rw [induced_degree_intersection,Set.inter_eq_left.mpr sub]
  exact (Nat.card_coe_set_eq _).symm

theorem join_closed_degree_stages {X:Type*} [Finite X] (G:SimpleGraph X) (U:Set X) (D:ℕ)
    (closed:∀x∈U,∀y,G.Adj x y → y∈U) (A:Set U) (B:Set ↥(Uᶜ:Set X))
    (inside:CompleteDegreeStage (G.induce U) D A) (outside:CompleteDegreeStage (G.induce Uᶜ) D B) :
    let S := (Subtype.val '' A)∪(Subtype.val '' B)
    CompleteDegreeStage G D S ∧ S.ncard=A.ncard+B.ncard := by
  intro S
  have comp (x:X) (hx:x∈Uᶜ) (y:X) (edge:G.Adj x y) : y∈Uᶜ := fun mem => hx (closed y mem x edge.symm)
  have apart : Disjoint (Subtype.val '' A) (Subtype.val '' B) :=
    Set.disjoint_left.mpr (by rintro _ ⟨x,_,rfl⟩ ⟨y,_,eq⟩;exact y.property (eq ▸ x.property))
  have count : S.ncard=A.ncard+B.ncard := by
    rw [Set.ncard_union_eq apart,Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_image_of_injective _ Subtype.val_injective]
  refine ⟨⟨?_,?_,?_⟩,count⟩
  · rintro _ (⟨x,hx,rfl⟩|⟨x,hx,rfl⟩) _ (⟨y,hy,rfl⟩|⟨y,hy,rfl⟩) ne edge
    · exact inside.1 hx hy (fun eq => ne (congrArg Subtype.val eq)) edge
    · exact y.property (closed _ x.property _ edge)
    · exact x.property (closed _ y.property _ edge.symm)
    · exact outside.1 hx hy (fun eq => ne (congrArg Subtype.val eq)) edge
  · rintro _ (⟨x,hx,rfl⟩|⟨y,hy,rfl⟩)
    · exact (closed_set_degree_eq G U closed x).symm.trans (inside.2.1 x hx)
    · exact (closed_set_degree_eq G Uᶜ comp y).symm.trans (outside.2.1 y hy)
  · intro v full
    by_cases h:v∈U
    · let x:U := ⟨v,h⟩
      rcases inside.2.2 x ((closed_set_degree_eq G U closed x).trans full) with mem|⟨w,hw,adj⟩
      · exact Or.inl (Or.inl ⟨x,mem,rfl⟩)
      · exact Or.inr ⟨w.val,Or.inl ⟨w,hw,rfl⟩,adj⟩
    · let x:↥(Uᶜ:Set X) := ⟨v,h⟩
      rcases outside.2.2 x ((closed_set_degree_eq G Uᶜ comp x).trans full) with mem|⟨w,hw,adj⟩
      · exact Or.inl (Or.inr ⟨x,mem,rfl⟩)
      · exact Or.inr ⟨w.val,Or.inr ⟨w,hw,rfl⟩,adj⟩

theorem strict_six_shadow_on_actual_exterior (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (U:Set F.X) (closed:∀x∈U,∀y,F.G.Adj x y → y∈U)
    (A:Set U) (B:Set ↥(Uᶜ:Set F.X)) (inside:CompleteDegreeStage (F.G.induce U) 6 A)
    (outside:CompleteDegreeStage (F.G.induce Uᶜ) 6 B) :
    widthAt F.n F.m F.r 6≤A.ncard+B.ncard+(2*highestWidth F.n F.m F.r+10)/3 := by
  obtain ⟨stage,count⟩ := join_closed_degree_stages F.G U 6 closed A B inside outside
  have bound := (strict_six_complete_stage_shadow F paid six _ stage).2.2.1
  rw [count] at bound
  omega

#print axioms closed_set_degree_eq
#print axioms join_closed_degree_stages
#print axioms strict_six_shadow_on_actual_exterior
end JSP452Audit.StarHost
