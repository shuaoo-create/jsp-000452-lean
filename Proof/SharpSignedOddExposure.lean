import GeneralExposureLabelOwnership
namespace JSP452Audit.StarHost
open SimpleGraph

theorem positive_label_layers {X A:Type*} [Finite X] [Finite A] (m:ℕ) (pos:0<m) (Q:SimpleGraph X) (t:A→X)
    (cap:∀v,Nat.card (Q.neighborSet v)+Nat.card {a:A // t a=v}≤2*m) :
    ∃V:TwoDegreeLayers Q m,∃owner:A→Fin m,
      (Finset.univ.filter (fun j => Odd (({a:A|owner a=j}:Set _).ncard))).card≤1 ∧
      (∀j v,((V.part j).neighborSet v).ncard+({a:A|owner a=j ∧ t a=v}:Set _).ncard≤2) := by
  cases m with
  | zero => omega
  | succ k => exact PairedLayers.all_label_layers k Q t cap

theorem actual_odd_sharp_signed_width {X:Type*} [Finite X] (G:SimpleGraph X) (r s:ℕ) (hs:0<s)
    (cap:∀v,Nat.card (G.neighborSet v)≤2*(r+s)+1) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 2*r+2)) (forest (fun _:Fin v => 2*s+1))) :
    let l := u+v-1
    l+2*r*((l-1)/(2*s)+1)≤minimumExposure G (2*(r+s)+1) := by
  obtain ⟨L⟩ := positive_exposure_labels_exist G (2*(r+s)+1) (by omega)
  have cap' (x:X) : Nat.card (L.base.neighborSet x)+Nat.card {a:↥L.W // L.tip a=x}≤2*(r+s) := by
    have b := L.residual_degree_with_ports cap x
    have eq : L.fiber Set.univ x={a:↥L.W|L.tip a=x} := by ext a;simp [ExposureLabels.fiber]
    rw [eq] at b;exact b
  obtain ⟨V,c,par,paid⟩ := positive_label_layers (r+s) (by omega) L.base L.tip cap'
  exact L.degree_split_signed_width V c paid par hs u v hu hv force

theorem seven_signed_three_six {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤7) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 6)) (forest (fun _:Fin v => 3))) :
    let l := u+v-1
    l+4*((l-1)/2+1)≤minimumExposure G 7 :=
  actual_odd_sharp_signed_width G 2 1 (by decide) cap u v hu hv force

theorem seven_signed_four_five {X:Type*} [Finite X] (G:SimpleGraph X)
    (cap:∀v,Nat.card (G.neighborSet v)≤7) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 4)) (forest (fun _:Fin v => 5))) :
    let l := u+v-1
    l+2*((l-1)/4+1)≤minimumExposure G 7 :=
  actual_odd_sharp_signed_width G 1 2 (by decide) cap u v hu hv force

#print axioms positive_label_layers
#print axioms actual_odd_sharp_signed_width
#print axioms seven_signed_three_six
#print axioms seven_signed_four_five
end JSP452Audit.StarHost
