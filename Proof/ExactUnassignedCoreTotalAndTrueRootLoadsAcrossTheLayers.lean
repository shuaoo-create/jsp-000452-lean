import AssignEveryRequiredRootAndEveryCoreToTheirActualLayers
namespace JSP452Audit.StarHost.ActualAssignmentLayers
open SimpleGraph
universe u v
variable {R:Type u} {C:Type v} [Finite R] [Finite C] {L:R→C→Prop} {w:R→ℕ} {k:ℕ}
variable {M:(portIncidenceGraph (slotIncidence L w k)).Subgraph} {hm:M.IsMatching} {A:Set R} (B:ActualAssignmentLayers hm A)
abbrev ids (t:Fin k) := {e:PortMatching.cores M|B.colour e=t}
def assigned (t:Fin k) : Set C := (fun i:PortMatching.cores M => i.val.1) '' B.ids t
noncomputable def loadAt (t:Fin k) (r:R) : ℕ :=
  ({i:PortMatching.cores M|B.colour i=t ∧ (PortMatching.mates hm i).val.1=r}:Set _).ncard

theorem count_assigned (t:Fin k) : (B.assigned t).ncard=(B.ids t).ncard := by
  apply Set.InjOn.ncard_image
  intro x inside y same eq
  exact B.coreUnique x y (inside.trans same.symm) eq

theorem total_missing :
    (∑t:Fin k,((B.assigned t)ᶜ:Set C).ncard)=((PortMatching.cores M)ᶜ:Set (CoreSlots C k)).ncard := by
  classical
  have slices : (∑t:Fin k,(B.assigned t).ncard)=(PortMatching.cores M).ncard := by
    simp_rw [B.count_assigned]
    have eq := Nat.card_congr (Equiv.sigmaFiberEquiv B.colour)
    rw [Nat.card_sigma,Nat.card_coe_set_eq] at eq
    exact eq
  have all := Finset.sum_congr (s₁:=Finset.univ) rfl (fun (t:Fin k) _ => Set.ncard_add_ncard_compl (B.assigned t))
  rw [Finset.sum_add_distrib,slices,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] at all
  have slots := Set.ncard_add_ncard_compl (PortMatching.cores M)
  change _=Nat.card (C×Fin k) at slots
  rw [Nat.card_prod,Nat.card_fin,Nat.mul_comm] at slots
  omega

theorem root_load_total (r:R) : (∑t:Fin k,B.loadAt t r)≤w r := by
  classical
  let a := PortMatching.mates hm
  let F : Set (PortMatching.cores M) := {i|(a i).val.1=r}
  let eq : (Σt:Fin k,↥({i:PortMatching.cores M|B.colour i=t ∧ (a i).val.1=r}:Set _)) ≃ ↥F := {
    toFun := fun ⟨_,x⟩ => ⟨x.val,x.property.2⟩
    invFun := fun i => ⟨B.colour i.val,⟨i.val,rfl,i.property⟩⟩
    left_inv := by rintro ⟨t,x,dt,hx⟩;subst t;rfl
    right_inv := fun _ => rfl}
  let index (i:↥F) : Fin (w r) := ⟨(a i.val).val.2.val,(a i.val).val.2.isLt.trans_eq (congrArg w i.property)⟩
  have inj : Function.Injective index := by
    intro i j e
    have ea : (a i.val).val.1=(a j.val).val.1 := i.property.trans j.property.symm
    have eb : (a i.val).val.2.val=(a j.val).val.2.val := congrArg Fin.val e
    have equal {v z:RootSlots w} (first:v.1=z.1) (second:v.2.val=z.2.val) : v=z := by
      rcases v with ⟨x,p⟩;rcases z with ⟨y,q⟩
      change x=y at first;subst y
      exact congrArg (fun b:Fin (w x) => (⟨x,b⟩:RootSlots w)) (Fin.ext second)
    exact Subtype.ext (a.injective (Subtype.ext (equal ea eb)))
  have quota := Nat.card_le_card_of_injective index inj
  rw [Nat.card_fin] at quota
  have total := Nat.card_congr eq
  rw [Nat.card_sigma] at total
  change (∑t:Fin k,Nat.card ↥({i:PortMatching.cores M|B.colour i=t ∧ (a i).val.1=r}:Set _))=Nat.card ↥F at total
  dsimp only [loadAt];simp_rw [←Nat.card_coe_set_eq]
  exact total.le.trans quota

#print axioms count_assigned
#print axioms total_missing
#print axioms root_load_total
end JSP452Audit.StarHost.ActualAssignmentLayers
