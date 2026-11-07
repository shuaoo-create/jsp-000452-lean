import LargeDegreeDominatingAccount
namespace JSP452Audit.StarHost

/-- Three states select the left label, three select the right label, and
four leave their common coordinate empty. -/
def pairMaskSelect (side : Bool) (z : Fin 10) : Prop :=
  if side then 3≤z.val ∧ z.val<6 else z.val<3

instance (side : Bool) (z : Fin 10) : Decidable (pairMaskSelect side z) := by
  unfold pairMaskSelect;split <;> infer_instance

def pairAllowed (tags : Finset Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun z => ∀b∈tags,¬pairMaskSelect b z)

/-- All four possible subsets of a matched coordinate are counted exactly. -/
theorem pair_allowed_card (tags : Finset Bool) : (pairAllowed tags).card=10-3*tags.card := by
  have all : ∀S:Finset Bool,(pairAllowed S).card=10-3*S.card := by decide
  exact all tags

theorem pair_allowed_rate (tags : Finset Bool) :
    ((pairAllowed tags).card:ℚ)/10≤(7/10:ℚ)^tags.card := by
  rw [pair_allowed_card]
  have le : tags.card≤2 := (Finset.card_le_univ tags).trans (by decide)
  rcases (show tags.card=0 ∨ tags.card=1 ∨ tags.card=2 by omega) with h|h|h <;> rw [h] <;> norm_num

theorem pair_allowed_discount (tags : Finset Bool) (two : tags.card=2) :
    ((pairAllowed tags).card:ℚ)/10=(40/49:ℚ)*(7/10:ℚ)^tags.card := by
  rw [pair_allowed_card,two];norm_num

/-- Finite count of independent ten-state coordinates, each with a possibly
different set of permitted states. -/
theorem paired_coordinate_weight {I : Type*} [Fintype I] (C : I→Finset (Fin 10)) :
    (Nat.card {f:I→Fin 10 // ∀i,f i∈C i}:ℚ)=
      (10:ℚ)^(Nat.card I)*∏i:I,((C i).card:ℚ)/10 := by
  classical
  let A := {f:I→Fin 10 // ∀i,f i∈C i}
  let e : A ≃ ((i:I)→↥(C i)) := {
    toFun := fun f i => ⟨f.val i,f.property i⟩
    invFun := fun g => ⟨fun i => (g i).val,fun i => (g i).property⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  have card := Nat.card_congr e
  rw [Nat.card_pi] at card
  have fi (i:I) : Nat.card ↥(C i)=(C i).card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  simp_rw [fi] at card
  change Nat.card A=∏i:I,(C i).card at card
  change (Nat.card A:ℚ)=_
  rw [card,Nat.cast_prod,Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Nat.card_eq_fintype_card]
  field_simp

#print axioms pair_allowed_card
#print axioms pair_allowed_rate
#print axioms pair_allowed_discount
#print axioms paired_coordinate_weight
end JSP452Audit.StarHost
