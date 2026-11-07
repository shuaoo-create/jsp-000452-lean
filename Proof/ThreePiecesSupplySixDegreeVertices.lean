import ConnectedPieceIndependentUnion
namespace JSP452Audit.StarHost
open SimpleGraph

theorem three_piece_independent_supply {X:Type*} [Finite X] (G:SimpleGraph X) (S:Set X)
    (T:Set (G.induce Sᶜ).ConnectedComponent) (Z b:ℕ) (many:T.ncard=3)
    (order:∀c∈T,2*Z+1≤Nat.card c.supp) (cap:∀v,Nat.card (G.neighborSet v)≤6)
    (need:b≤Z) : ∃U:Set X,U⊆regionCore G S T ∧ G.IsIndepSet U ∧ U.ncard=b := by
  classical
  let _ := Fintype.ofFinite T
  let H := G.induce Sᶜ
  have localCap (v:↥(Sᶜ : Set X)) : Nat.card (H.neighborSet v)≤6 :=
    (induced_neighbor_count_le G Sᶜ v).trans (cap v.val)
  obtain ⟨J,inside,ind,room⟩ := independent_union_of_components H 6 localCap T
  have count : Fintype.card T=3 := (Nat.card_eq_fintype_card (α:=T)).symm.trans many
  have floor := Finset.sum_le_sum (s:=(Finset.univ:Finset T)) (f:=fun _ => 2*Z)
    (g:=fun c => Nat.card c.val.supp-1) (fun c _ => by have := order c.val c.property;omega)
  simp only [Finset.sum_const,Finset.card_univ,count,nsmul_eq_mul] at floor
  have enough : b≤J.ncard := by omega
  obtain ⟨I,sub,card⟩ := Set.exists_subset_card_eq enough
  refine ⟨Subtype.val '' I,?_,?_,(Set.ncard_image_of_injective _ Subtype.val_injective).trans card⟩
  · rintro _ ⟨v,hv,rfl⟩
    exact ⟨v,rfl,inside v (sub hv)⟩
  · rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩ ne edge
    exact ind (sub hv) (sub hw) (fun eq => ne (congrArg Subtype.val eq)) edge

#print axioms three_piece_independent_supply
end JSP452Audit.StarHost
