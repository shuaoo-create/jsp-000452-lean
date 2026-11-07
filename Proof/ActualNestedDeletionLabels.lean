import ShortStagesOnSelectedSixComponents
namespace JSP452Audit.StarHost
open SimpleGraph

def nestedRemoved {X:Type*} (A:Set X) (B:Set ↥(Aᶜ:Set X)) : Set X := A∪Subtype.val '' B

theorem nested_removed_card {X:Type*} [Finite X] (A:Set X) (B:Set ↥(Aᶜ:Set X)) :
    (nestedRemoved A B).ncard=A.ncard+B.ncard := by
  have apart : Disjoint A (Subtype.val '' B) := Set.disjoint_left.mpr (by rintro _ hx ⟨x,_,rfl⟩;exact x.property hx)
  rw [nestedRemoved,Set.ncard_union_eq apart,Set.ncard_image_of_injective _ Subtype.val_injective]

def nestedDeletionIso {X:Type*} (G:SimpleGraph X) (A:Set X) (B:Set ↥(Aᶜ:Set X)) :
    (G.induce Aᶜ).induce Bᶜ ≃g G.induce (nestedRemoved A B)ᶜ := by
  let send (x:↥(Bᶜ : Set ↥(Aᶜ:Set X))) : ↥((nestedRemoved A B)ᶜ : Set X) :=
    ⟨x.val.val,by
      rintro (ha|⟨y,hy,eq⟩)
      · exact x.val.property ha
      · exact x.property ((Subtype.ext eq : y=x.val) ▸ hy)⟩
  let back (x:↥((nestedRemoved A B)ᶜ : Set X)) : ↥(Bᶜ : Set ↥(Aᶜ:Set X)) :=
    let v:↥(Aᶜ:Set X) := ⟨x.val,fun ha => x.property (Or.inl ha)⟩
    ⟨v,fun hv => x.property (Or.inr ⟨v,hv,rfl⟩)⟩
  exact { toEquiv := {toFun := send,invFun := back,left_inv := fun _ => rfl,right_inv := fun _ => rfl}
          map_rel_iff' := Iff.rfl }

theorem nested_deletion_edges {X:Type*} [Finite X] (G:SimpleGraph X) (A:Set X) (B:Set ↥(Aᶜ:Set X)) :
    ((G.induce Aᶜ).induce Bᶜ).edgeSet.ncard=(G.induce (nestedRemoved A B)ᶜ).edgeSet.ncard :=
  Nat.card_congr (nestedDeletionIso G A B).mapEdgeSet

theorem nested_deletion_cap {X:Type*} [Finite X] (G:SimpleGraph X) (A:Set X) (B:Set ↥(Aᶜ:Set X)) (D:ℕ)
    (cap:∀x,Nat.card (((G.induce Aᶜ).induce Bᶜ).neighborSet x)≤D) :
    ∀v,Nat.card ((G.induce (nestedRemoved A B)ᶜ).neighborSet v)≤D := by
  let e := nestedDeletionIso G A B
  intro v
  let x := e.symm v
  have bound := cap x
  have eq := Nat.card_congr (e.mapNeighborSet x)
  change Nat.card (((G.induce Aᶜ).induce Bᶜ).neighborSet x)=Nat.card ((G.induce (nestedRemoved A B)ᶜ).neighborSet (e x)) at eq
  have same : e x=v := e.apply_symm_apply v
  rwa [eq,same] at bound

#print axioms nested_removed_card
#print axioms nested_deletion_edges
#print axioms nested_deletion_cap
end JSP452Audit.StarHost
