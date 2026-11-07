import OriginalStrictDegreeSevenExcluded
namespace JSP452Audit.StarHost
open SimpleGraph

theorem half_cap_piece_independent_supply {X:Type*} [Finite X] (G:SimpleGraph X) (S:Set X)
    (T:Set (G.induce Sᶜ).ConnectedComponent) (p Z b:ℕ) (pos:0<p) (many:T.ncard=p)
    (order:∀c∈T,2*Z+1≤Nat.card c.supp) (cap:∀v,Nat.card (G.neighborSet v)≤2*p)
    (need:b≤Z) : ∃U:Set X,U⊆regionCore G S T ∧ G.IsIndepSet U ∧ U.ncard=b := by
  classical
  let _ := Fintype.ofFinite T
  let H := G.induce Sᶜ
  have localCap (v:↥(Sᶜ : Set X)) : Nat.card (H.neighborSet v)≤2*p :=
    (induced_neighbor_count_le G Sᶜ v).trans (cap v.val)
  obtain ⟨J,inside,ind,room⟩ := independent_union_of_components H (2*p) localCap T
  have count : Fintype.card T=p := (Nat.card_eq_fintype_card (α:=T)).symm.trans many
  have floor := Finset.sum_le_sum (s:=(Finset.univ:Finset T)) (f:=fun _ => 2*Z)
    (g:=fun c => Nat.card c.val.supp-1) (fun c _ => by have := order c.val c.property;omega)
  simp only [Finset.sum_const,Finset.card_univ,count,nsmul_eq_mul] at floor
  have scaled : (2*p)*Z≤(2*p)*J.ncard := by
    have eq : p*(2*Z)=2*p*Z := by ring
    change p*(2*Z)≤_ at floor
    rw [eq] at floor
    exact floor.trans room
  have enough : b≤J.ncard := need.trans ((Nat.le_of_mul_le_mul_left scaled (by omega)))
  obtain ⟨I,sub,card⟩ := Set.exists_subset_card_eq enough
  refine ⟨Subtype.val '' I,?_,?_,(Set.ncard_image_of_injective _ Subtype.val_injective).trans card⟩
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨v,rfl,inside v (sub hv)⟩
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
    exact ind (sub hv) (sub hw) (fun eq => ne (congrArg Subtype.val eq)) edge

#print axioms half_cap_piece_independent_supply
end JSP452Audit.StarHost
