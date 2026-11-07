import EvenCapTwoLayerDecomposition
namespace JSP452Audit.StarHost.ExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} {D m:ℕ} (L:ExposureLabels G D)

def ownerSet (owner:↥L.W→Fin m) (T:Finset (Fin m)) : Set ↥L.W := {u|owner u∈T}

theorem degree_and_label_subset (V:TwoDegreeLayers L.base m) (owner:↥L.W→Fin m)
    (paid:∀i v,((V.part i).neighborSet v).ncard+(L.fiber {u|owner u=i} v).ncard≤2)
    (T:Finset (Fin m)) (v:X) :
    ((T.sup V.part).neighborSet v).ncard+(L.fiber (L.ownerSet owner T) v).ncard≤2*T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have no : L.fiber (L.ownerSet owner ∅) v=∅ := Set.eq_empty_of_forall_notMem (fun _ h => Finset.notMem_empty _ h.1)
    simp [no]
  | @insert i T fresh ih =>
    have labels : L.fiber (L.ownerSet owner (insert i T)) v=L.fiber {u|owner u=i} v∪L.fiber (L.ownerSet owner T) v := by
      ext u
      change (owner u∈insert i T ∧ L.tip u=v) ↔ (owner u=i ∧ L.tip u=v) ∨ (owner u∈T ∧ L.tip u=v)
      rw [Finset.mem_insert];tauto
    have lcost := Set.ncard_union_le (L.fiber {u|owner u=i} v) (L.fiber (L.ownerSet owner T) v)
    have edges : ((V.part i⊔T.sup V.part).neighborSet v).ncard≤((V.part i).neighborSet v).ncard+((T.sup V.part).neighborSet v).ncard :=
      Set.ncard_union_le _ _
    have new := paid i v
    rw [Finset.sup_insert,Finset.card_insert_of_notMem fresh,labels]
    omega

theorem chosen_blue_layers_need_width (V:TwoDegreeLayers L.base m) (owner:↥L.W→Fin m)
    (paid:∀i v,((V.part i).neighborSet v).ncard+(L.fiber {u|owner u=i} v).ncard≤2)
    (T:Finset (Fin m)) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 2*Tᶜ.card+2)) (forest (fun _:Fin v => 2*T.card+1))) :
    u+v-1≤(L.ownerSet owner T).ncard := by
  classical
  let R := Tᶜ.sup V.part
  have sub : R≤L.base := Finset.sup_le (fun i _ => V.sub i)
  have other : L.base \ R≤T.sup V.part := by
    intro x y edge
    obtain ⟨i,part⟩ := V.cover x y edge.1
    by_cases mem:i∈T
    · exact (Finset.le_sup (f:=V.part) mem) part
    · exact (edge.2 ((Finset.le_sup (f:=V.part) (Finset.mem_compl.mpr mem)) part)).elim
  have blue (x:X) : Nat.card ((L.base \ R).neighborSet x)≤2*T.card := by
    have inc : (L.base \ R).neighborSet x⊆(T.sup V.part).neighborSet x := fun _ e => other e
    have price := L.degree_and_label_subset V owner paid T x
    exact (Set.ncard_le_ncard inc).trans ((Nat.le_add_right _ _).trans price)
  have need := L.actual_labels_force_complement R sub (L.ownerSet owner Tᶜ)
    (L.degree_and_label_subset V owner paid Tᶜ) blue u v hu hv force
  have eq : (L.ownerSet owner Tᶜ)ᶜ=L.ownerSet owner T := by ext u;simp [ownerSet]
  rwa [eq] at need

#print axioms degree_and_label_subset
#print axioms chosen_blue_layers_need_width
end JSP452Audit.StarHost.ExposureLabels
