import SignedLayerCountArithmetic
namespace JSP452Audit.StarHost.ExposureLabels
open SimpleGraph
variable {X:Type*} [Finite X] {G:SimpleGraph X} {D m:ℕ} (L:ExposureLabels G D)

theorem owner_set_card_eq_sum (owner:↥L.W→Fin m) (T:Finset (Fin m)) :
    (L.ownerSet owner T).ncard=∑i∈T,({u:↥L.W|owner u=i}:Set _).ncard := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [ownerSet]
  | @insert i T fresh ih =>
    have eq : L.ownerSet owner (insert i T)={u|owner u=i}∪L.ownerSet owner T := by
      ext u;simp [ownerSet]
    have dis : Disjoint ({u:↥L.W|owner u=i}:Set _) (L.ownerSet owner T) := by
      apply Set.disjoint_left.mpr
      intro u hi hu
      exact fresh ((show owner u=i from hi) ▸ (show owner u∈T from hu))
    rw [eq,Set.ncard_union_eq dis,Finset.sum_insert fresh,ih]

theorem degree_split_signed_width {r s:ℕ} (V:TwoDegreeLayers L.base (r+s)) (owner:↥L.W→Fin (r+s))
    (paid:∀i v,((V.part i).neighborSet v).ncard+(L.fiber {u|owner u=i} v).ncard≤2)
    (oddCount:(Finset.univ.filter (fun i => Odd (({u:↥L.W|owner u=i}:Set _).ncard))).card≤1)
    (haveS:0<s) (u v:ℕ) (hu:0<u) (hv:0<v)
    (force:Forces G (forest (fun _:Fin u => 2*r+2)) (forest (fun _:Fin v => 2*s+1))) :
    u+v-1+2*r*((u+v-1-1)/(2*s)+1)≤minimumExposure G D := by
  classical
  let w := fun i:Fin (r+s) => ({z:↥L.W|owner z=i}:Set _).ncard
  have all (T:Finset (Fin (r+s))) (size:T.card=s) : u+v-1≤∑i∈T,w i := by
    have comp : Tᶜ.card=r := by rw [Finset.card_compl,Fintype.card_fin,size];omega
    have need := L.chosen_blue_layers_need_width V owner paid T u v hu hv (by rwa [comp,size])
    exact (L.owner_set_card_eq_sum owner T) ▸ need
  have result := signed_layer_count_bound w (by omega : 0<u+v-1) haveS oddCount all
  have total := L.owner_set_card_eq_sum owner Finset.univ
  have eq : L.ownerSet owner Finset.univ=Set.univ := by ext u;simp [ownerSet]
  rw [eq,Set.ncard_univ] at total
  change Nat.card ↥L.W=∑i,w i at total
  rw [←total] at result
  exact result.trans (le_of_eq L.optimal)

#print axioms owner_set_card_eq_sum
#print axioms degree_split_signed_width
end JSP452Audit.StarHost.ExposureLabels
