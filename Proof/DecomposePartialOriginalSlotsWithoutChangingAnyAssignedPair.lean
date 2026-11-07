import ColourAllActualRegularEdgeIdsWithoutEndpointConflicts
import Mathlib.Logic.Equiv.Fintype
namespace JSP452Audit.StarHost
universe u v w

theorem extend_two_named_embeddings {I X:Type*} [Finite X] (left right:I↪X) :
    ∃e:Equiv.Perm X,∀i,e (left i)=right i := by
  classical
  let first := Equiv.ofInjective left left.injective
  let last := Equiv.ofInjective right right.injective
  let between : ↥(Set.range left) ≃ ↥(Set.range right) := first.symm.trans last
  let e := between.extendSubtype
  refine ⟨e,fun i => ?_⟩
  have maintained := between.extendSubtype_apply_of_mem (left i) (Set.mem_range_self i)
  change e (left i)=(between (first i)).val at maintained
  have exact : between (first i)=last i := by simp [between]
  rw [exact] at maintained;exact maintained

theorem colour_partial_endpoint_slots {I:Type u} {A:Type v} {B:Type w} [Finite A] [Finite B] (k:ℕ)
    (left:I↪A×Fin k) (right:I↪B×Fin k) :
    ∃colour:I→Fin k,∀i j,colour i=colour j → (left i).1=(left j).1 ∨ (right i).1=(right j).1 → i=j := by
  classical
  let V := A⊕B
  let liftL (x:A×Fin k) : V×Fin k := (.inl x.1,x.2)
  let liftR (x:B×Fin k) : V×Fin k := (.inr x.1,x.2)
  have li : Function.Injective liftL := fun x y eq =>
    Prod.ext (Sum.inl.inj (congrArg Prod.fst eq)) (congrArg (fun e:V×Fin k => e.2) eq)
  have ri : Function.Injective liftR := fun x y eq =>
    Prod.ext (Sum.inr.inj (congrArg Prod.fst eq)) (congrArg (fun e:V×Fin k => e.2) eq)
  let l := left.trans (⟨liftL,li⟩:A×Fin k↪V×Fin k)
  let r := right.trans (⟨liftR,ri⟩:B×Fin k↪V×Fin k)
  obtain ⟨p,spec⟩ := extend_two_named_embeddings l r
  let src (e:V×Fin k) := e.1
  let dst (e:V×Fin k) := (p e).1
  have incoming (v:V) : Nat.card {e // dst e=v}=k := by
    let eq : {e // dst e=v} ≃ Fin k := {
      toFun := fun e => (p e.val).2
      invFun := fun i => ⟨p.symm (v,i),by simp [dst]⟩
      left_inv := by intro e;apply Subtype.ext;apply p.injective;rw [p.apply_symm_apply];exact Prod.ext e.property.symm rfl
      right_inv := by intro i;change (p (p.symm (v,i))).2=i;rw [p.apply_symm_apply]}
    exact (Nat.card_congr eq).trans (Nat.card_fin k)
  have outgoing (v:V) : Nat.card {e // src e=v}=k := by
    let eq : {e // src e=v} ≃ Fin k := {
      toFun := fun e => e.val.2
      invFun := fun i => ⟨(v,i),rfl⟩
      left_inv := fun e => Subtype.ext (Prod.ext e.property.symm rfl)
      right_inv := fun _ => rfl}
    exact (Nat.card_congr eq).trans (Nat.card_fin k)
  obtain ⟨col,unique⟩ := colour_regular_edge_ids k src dst outgoing incoming
  refine ⟨fun i => col (l i),?_⟩
  intro i j same hit
  apply l.injective (unique (l i) (l j) same ?_)
  rcases hit with leftEq|rightEq
  · exact Or.inl (congrArg Sum.inl leftEq)
  · right;change (p (l i)).1=(p (l j)).1;rw [spec,spec];exact congrArg Sum.inr rightEq

#print axioms extend_two_named_embeddings
#print axioms colour_partial_endpoint_slots
end JSP452Audit.StarHost
