import WholePairLayerOwnership
namespace JSP452Audit.StarHost.PairedLayers
open SimpleGraph

theorem even_label_layers {X A:Type*} [Finite X] [Finite A] (k:ℕ) (Q:SimpleGraph X) (t:A→X)
    (even:Even (Nat.card A))
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:A // t a=v}≤2*(k+1)) :
    ∃V:TwoDegreeLayers Q (k+1),∃owner:A→Fin (k+1),
      (∀j,Even (({a:A|owner a=j}:Set _).ncard)) ∧
      (∀j v,((V.part j).neighborSet v).ncard+({a:A|owner a=j ∧ t a=v}:Set _).ncard≤2) := by
  classical
  obtain ⟨n,size⟩ := even
  let _ := Fintype.ofFinite A
  let e : Fin n×Fin 2 ≃ A := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,←Nat.card_eq_fintype_card];omega)
  let tip (a:Fin n×Fin 2) := t (e a)
  have budget (v:X) : Nat.card (Q.neighborSet v)+Nat.card {a:Fin n×Fin 2 // tip a=v}≤2*(k+1) := by
    have E := Equiv.subtypeEquiv e (p:=fun a => tip a=v) (q:=fun a => t a=v) (fun _ => Iff.rfl)
    rw [Nat.card_congr E];exact cap v
  obtain ⟨V,c,paid⟩ := paired_port_layers k Q tip budget
  let owner (a:A) := c (e.symm a).1
  refine ⟨V,owner,?_,?_⟩
  · intro j
    let C := {a:A|owner a=j}
    let K := {i:Fin n|c i=j}
    let E : ↥C ≃ ↥K×Fin 2 := {
      toFun := fun a => (⟨(e.symm a.val).1,a.property⟩,(e.symm a.val).2)
      invFun := fun z => ⟨e (z.1.val,z.2),by change c (e.symm (e _)).1=j; rw [e.symm_apply_apply];exact z.1.property⟩
      left_inv := fun a => Subtype.ext (e.apply_symm_apply a.val)
      right_inv := fun z => by apply Prod.ext <;> simp }
    have eq := (Nat.card_congr E).trans (Nat.card_prod _ _)
    rw [Nat.card_fin] at eq
    change C.ncard=K.ncard*2 at eq
    exact ⟨K.ncard,by change C.ncard=_;omega⟩
  · intro j v
    have E := Equiv.subtypeEquiv e (p:=fun a => c a.1=j ∧ tip a=v)
      (q:=fun a => owner a=j ∧ t a=v) (fun a => by simp [owner,tip])
    have eq : ({a:Fin n×Fin 2|c a.1=j ∧ tip a=v}:Set _).ncard=({a:A|owner a=j ∧ t a=v}:Set _).ncard := Nat.card_congr E
    rw [←eq];exact paid j v

#print axioms even_label_layers
end JSP452Audit.StarHost.PairedLayers
