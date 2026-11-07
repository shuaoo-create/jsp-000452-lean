import OnlyTheTwoNineRectangleCanUnderpayTheTenthColumn
namespace JSP452Audit.StarHost.TenBlockPartition
open SimpleGraph
universe u v
variable {X:Type u} [Finite X] {G:SimpleGraph X} (R:TenBlockPartition G)

theorem even_cut_on_actual_components (w:ℕ) (room:w≤R.capacity) :
    ∃U:Set X,U⊆R.core ∧ U.ncard=2*w ∧
      ∀{I:Type v} [Fintype I] (m:I→ℕ),(forest m).IsContained (G.induce (R.core\U)) →
        (∑i,(m i+1)/2)≤R.capacity-w := by
  classical
  let H := G.induce R.core
  let _ := Fintype.ofFinite H.ConnectedComponent
  obtain ⟨V,card,quota⟩ := region_even_deletion_set H (fun c => (R.critical c).2) w room
  let U:Set X := Subtype.val '' V
  have count:U.ncard=2*w := (Set.ncard_image_of_injective V Subtype.val_injective).trans card
  refine ⟨U,?_,count,?_⟩
  · rintro _ ⟨x,_,rfl⟩;exact x.property
  intro I inst m copy
  obtain ⟨f⟩ := copy
  let send (z:Vertices m) : ↥(Vᶜ:Set R.core) :=
    ⟨⟨(f z).val,(f z).property.1⟩,fun mem => (f z).property.2 ⟨_,mem,rfl⟩⟩
  let g : (forest m).Copy (H.induce Vᶜ) :=
    {toHom := {toFun := send,map_rel' := fun e => f.toHom.map_adj e},
     injective' := fun _ _ e => f.injective (Subtype.ext (congrArg (fun z:↥(Vᶜ:Set R.core) => z.val.val) e))}
  have limit := critical_half_orders_off_cover H m V g (fun c => (R.critical c).2)
  rw [quota] at limit
  change _+w≤R.capacity at limit
  omega

#print axioms even_cut_on_actual_components
end JSP452Audit.StarHost.TenBlockPartition
