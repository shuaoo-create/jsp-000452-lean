import TheExteriorOfTheUniqueComponentHasScoreOne
open private JSP452Audit.StarHost.sumCompEquiv from LocalOddReplacement
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
def OddCriticalFamily {X:Type u} [Finite X] (G:SimpleGraph X) : Prop :=
  ∀c:G.ConnectedComponent,Odd (Nat.card c.supp) ∧ PerfectAfterEveryDeletion c.toSimpleGraph

theorem odd_critical_family_of_iso {X Y:Type u} [Finite X] [Finite Y] {G:SimpleGraph X} {H:SimpleGraph Y}
    (e:G≃g H) (critical:OddCriticalFamily G) : OddCriticalFamily H := by
  intro d
  obtain ⟨c,rfl⟩ := e.connectedComponentEquiv.surjective d
  let send := SimpleGraph.ConnectedComponent.isoEquivSupp e c
  let f : c.toSimpleGraph ≃g (e.connectedComponentEquiv c).toSimpleGraph := {
    toEquiv := send
    map_rel_iff' := fun {_ _} => e.map_rel_iff }
  exact ⟨(Nat.card_congr send) ▸ (critical c).1,perfect_after_deletion_of_iso f (critical c).2⟩

theorem odd_critical_family_sum {X Y:Type u} [Finite X] [Finite Y] (G:SimpleGraph X) (H:SimpleGraph Y)
    (left:OddCriticalFamily G) (right:OddCriticalFamily H) : OddCriticalFamily (G⊕g H) := by
  let e := JSP452Audit.StarHost.sumCompEquiv G H
  have mem (z:X⊕Y) (c:G.ConnectedComponent⊕H.ConnectedComponent) :
      z∈(e.symm c).supp ↔ Sum.elim (fun x => Sum.inl (G.connectedComponentMk x))
        (fun y => Sum.inr (H.connectedComponentMk y)) z=c := by
    change (G⊕g H).connectedComponentMk z=e.symm c ↔ _
    rw [←e.injective.eq_iff,e.apply_symm_apply];cases z <;> rfl
  intro c
  obtain ⟨d,rfl⟩ := e.symm.surjective c
  cases d with
  | inl d =>
    let f (x:↥d.supp) : ↥(e.symm (Sum.inl d)).supp := ⟨Sum.inl x.val,(mem _ _).mpr (congrArg Sum.inl x.property)⟩
    have onto : Function.Surjective f := by
      rintro ⟨x,hx⟩;rcases x with x|x
      · have eq := (mem _ _).mp hx
        exact ⟨⟨x,Sum.inl.inj eq⟩,rfl⟩
      · exact (Sum.inr_ne_inl ((mem _ _).mp hx)).elim
    have inj : Function.Injective f := fun _ _ h => Subtype.ext (Sum.inl.inj (congrArg Subtype.val h))
    let iso : d.toSimpleGraph ≃g (e.symm (Sum.inl d)).toSimpleGraph := {
      toEquiv := Equiv.ofBijective f ⟨inj,onto⟩
      map_rel_iff' := Iff.rfl }
    exact ⟨(Nat.card_congr iso.toEquiv) ▸ (left d).1,perfect_after_deletion_of_iso iso (left d).2⟩
  | inr d =>
    let f (x:↥d.supp) : ↥(e.symm (Sum.inr d)).supp := ⟨Sum.inr x.val,(mem _ _).mpr (congrArg Sum.inr x.property)⟩
    have onto : Function.Surjective f := by
      rintro ⟨x,hx⟩;rcases x with x|x
      · exact (Sum.inl_ne_inr ((mem _ _).mp hx)).elim
      · have eq := (mem _ _).mp hx
        exact ⟨⟨x,Sum.inr.inj eq⟩,rfl⟩
    have inj : Function.Injective f := fun _ _ h => Subtype.ext (Sum.inr.inj (congrArg Subtype.val h))
    let iso : d.toSimpleGraph ≃g (e.symm (Sum.inr d)).toSimpleGraph := {
      toEquiv := Equiv.ofBijective f ⟨inj,onto⟩
      map_rel_iff' := Iff.rfl }
    exact ⟨(Nat.card_congr iso.toEquiv) ▸ (right d).1,perfect_after_deletion_of_iso iso (right d).2⟩

#print axioms odd_critical_family_of_iso
#print axioms odd_critical_family_sum
end JSP452Audit.StarHost
