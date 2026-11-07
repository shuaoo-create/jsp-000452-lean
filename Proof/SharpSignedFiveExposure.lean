import PairPortPaletteRestriction
namespace JSP452Audit.StarHost.FiveExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} (L:FiveExposureLabels G)

theorem even_labels_paired_split (cap:∀v,Nat.card (G.neighborSet v)≤5) (even:Even L.W.ncard) :
    ∃R:SimpleGraph X,R≤L.base ∧ ∃A:Set ↥L.W,Even A.ncard ∧
      (∀v,(R.neighborSet v).ncard+(L.fiber A v).ncard≤2) ∧
      (∀v,((L.base \ R).neighborSet v).ncard+(L.fiber Aᶜ v).ncard≤2) := by
  classical
  obtain ⟨k,size⟩ := even
  let _ := Fintype.ofFinite ↥L.W
  let e : Fin k×Fin 2 ≃ ↥L.W := Fintype.equivOfCardEq (by
    rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin,←Nat.card_eq_fintype_card]
    change k*2=L.W.ncard;omega)
  let tip (a:Fin k×Fin 2) := L.tip (e a)
  have budget (v:X) : Nat.card (L.base.neighborSet v)+Nat.card {a:Fin k×Fin 2 // tip a=v}≤4 := by
    have equiv := Equiv.subtypeEquiv e (p:=fun a => tip a=v) (q:=fun u => u∈L.fiber Set.univ v)
      (fun a => by change tip a=v ↔ e a∈Set.univ ∧ tip a=v;simp)
    rw [Nat.card_congr equiv]
    exact L.residual_degree_with_ports cap v
  obtain ⟨R,sub,K,red,blue⟩ := paired_port_split L.base tip budget
  let A := {u:↥L.W|(e.symm u).1∈K}
  let indexed : ↥A ≃ ↥K×Fin 2 := {
    toFun := fun u => (⟨(e.symm u.val).1,u.property⟩,(e.symm u.val).2)
    invFun := fun v => ⟨e (v.1.val,v.2),by change (e.symm (e _)).1∈K;simp⟩
    left_inv := fun u => Subtype.ext (e.apply_symm_apply u.val)
    right_inv := fun v => by apply Prod.ext <;> simp }
  have pairOrder := (Nat.card_congr indexed).trans (Nat.card_prod _ _)
  rw [Nat.card_fin] at pairOrder
  change A.ncard=K.ncard*2 at pairOrder
  refine ⟨R,sub,A,⟨K.ncard,by omega⟩,?_,?_⟩
  · intro v
    have equiv := Equiv.subtypeEquiv e (p:=fun a => a.1∈K ∧ tip a=v) (q:=fun u => u∈L.fiber A v)
      (fun a => by change _ ↔ (e.symm (e a)).1∈K ∧ tip a=v;simp)
    have num : ({a:Fin k×Fin 2|a.1∈K ∧ tip a=v}:Set _).ncard=(L.fiber A v).ncard := Nat.card_congr equiv
    rw [←num];exact red v
  · intro v
    have equiv := Equiv.subtypeEquiv e (p:=fun a => a.1∉K ∧ tip a=v) (q:=fun u => u∈L.fiber Aᶜ v)
      (fun a => by change _ ↔ (e.symm (e a)).1∉K ∧ tip a=v;simp)
    have num : ({a:Fin k×Fin 2|a.1∉K ∧ tip a=v}:Set _).ncard=(L.fiber Aᶜ v).ncard := Nat.card_congr equiv
    rw [←num];exact blue v

end JSP452Audit.StarHost.FiveExposureLabels
namespace JSP452Audit.StarHost
open SimpleGraph

theorem actual_five_sharp_signed_width {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤5) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 3))) :
    let l := u+v-1
    l+2*((l+1)/2)≤minimumExposure G 5 := by
  obtain ⟨L⟩ := five_exposure_labels_exist G
  by_cases even : Even L.W.ncard
  · obtain ⟨R,sub,A,ev,r,b⟩ := L.even_labels_paired_split cap even
    exact L.paired_label_exposure_bound R sub A r b (Or.inl ev) u v hu hv force
  · obtain ⟨R,sub,A,r,b⟩ := L.actual_unpaired_label_split cap
    have total := Set.ncard_add_ncard_compl A
    change A.ncard+Aᶜ.ncard=L.W.ncard at total
    have ev : Even A.ncard ∨ Even Aᶜ.ncard := by
      by_contra! neither
      obtain ⟨a,oa⟩ := Nat.not_even_iff_odd.mp neither.1
      obtain ⟨b,ob⟩ := Nat.not_even_iff_odd.mp neither.2
      exact even ⟨a+b+1,by omega⟩
    exact L.paired_label_exposure_bound R sub A r b ev u v hu hv force

#print axioms FiveExposureLabels.even_labels_paired_split
#print axioms actual_five_sharp_signed_width
end JSP452Audit.StarHost
