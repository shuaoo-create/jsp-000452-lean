import CubicResidualMatchingBase
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Fintype X]

def cubicDoubleBlue (G:SimpleGraph X) (U:Set X) : Set X :=
  {x | x∉U ∧ fourWhiteDegree G U x=2}

/-- Twice-seeing old blue vertices provide real two-endpoint labels. Distinct
blue vertices stay distinct even when they have the same two white neighbours. -/
theorem cubic_terminal_pairs (G:SimpleGraph X) (U:Set X) [Fintype ↥(cubicDoubleBlue G U)]
    (reg : ∀x,Nat.card (G.neighborSet x)=3) :
    ∃P:CubicPairFamily X ↥(cubicDoubleBlue G U),
      (∀j,P.left j∈U ∧ P.right j∈U ∧ G.Adj (P.left j) j.val ∧ G.Adj (P.right j) j.val) ∧
      (∀v∈U,fourWhiteDegree G U v+P.degree U v≤3) ∧
      (P.active U).card=(cubicDoubleBlue G U).ncard := by
  classical
  let D := cubicDoubleBlue G U
  have two (j:↥D) : (G.neighborSet j.val∩U).ncard=2 := j.property.2
  choose l r ne both using fun j:↥D => Set.ncard_eq_two.mp (two j)
  let P : CubicPairFamily X ↥D := ⟨l,r,ne⟩
  have acts (j:↥D) : P.left j∈U ∧ P.right j∈U ∧ G.Adj (P.left j) j.val ∧ G.Adj (P.right j) j.val := by
    have x : l j∈G.neighborSet j.val∩U := by rw [both];simp
    have y : r j∈G.neighborSet j.val∩U := by rw [both];simp
    exact ⟨x.2,y.2,x.1.symm,y.1.symm⟩
  have all : P.active U=Finset.univ := by
    ext j
    simp only [P.mem_active,Finset.mem_univ,iff_true]
    exact ⟨(acts j).1,(acts j).2.1⟩
  have card : (P.active U).card=D.ncard := by rw [all,Finset.card_univ,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  refine ⟨P,acts,?_,card⟩
  intro x hx
  let A := (P.active U).filter (fun j => P.left j=x)
  let B := (P.active U).filter (fun j => P.right j=x)
  have separate : Disjoint A B := Finset.disjoint_left.mpr (fun j hj hb =>
    P.distinct j ((Finset.mem_filter.mp hj).2.trans (Finset.mem_filter.mp hb).2.symm))
  let N := G.neighborSet x∩Uᶜ
  have inside (j:↥(A∪B)) : j.val.val∈N := by
    have outside : j.val.val∉U := j.val.property.1
    rcases Finset.mem_union.mp j.property with left|right
    · have eq := (Finset.mem_filter.mp left).2
      exact ⟨eq ▸ (acts j.val).2.2.1,outside⟩
    · have eq := (Finset.mem_filter.mp right).2
      exact ⟨eq ▸ (acts j.val).2.2.2,outside⟩
  let send (j:↥(A∪B)) : ↥N := ⟨j.val.val,inside j⟩
  have inj := Nat.card_le_card_of_injective send (fun a b eq => Subtype.ext (Subtype.ext (congrArg
    (fun u:↥N => u.val) eq)))
  change Nat.card ↥(A∪B)≤Nat.card ↥N at inj
  have src : Nat.card ↥(A∪B)=(A∪B).card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]
  rw [src,Finset.card_union_of_disjoint separate,Nat.card_coe_set_eq] at inj
  change P.degree U x≤fourWhiteDegree G Uᶜ x at inj
  have sum := four_degree_split G U Uᶜ disjoint_compl_right x
  rw [Set.union_compl_self] at sum
  have tot : fourWhiteDegree G Set.univ x=3 := by
    unfold fourWhiteDegree;rw [Set.inter_univ,←Nat.card_coe_set_eq,reg]
  omega

/-- In the late phase the potential is exactly five times the remaining
order minus its ordinary-edge and labelled-pair cost. -/
theorem cubic_terminal_cost_identity {I : Type*} [Fintype I] (G:SimpleGraph X) (U:Set X) (P:CubicPairFamily X I)
    (reg : ∀x,Nat.card (G.neighborSet x)=3) (terminal : ∀x,fourWhiteDegree G U x≤2)
    (count : (P.active U).card=(cubicDoubleBlue G U).ncard) :
    cubicGroupPotential G U+P.residualCost G U=5*U.ncard := by
  classical
  let B := cubicDoubleBlue G U
  have eq (x:X) (outside:x∈Uᶜ) : fourWhiteDegree G U x=cubicBlueWeight (fourWhiteDegree G U x)+
      (if x∈B then 1 else 0) := by
    have small := terminal x
    by_cases yes:x∈B
    · have two : fourWhiteDegree G U x=2 := yes.2
      rw [if_pos yes,two];rfl
    · have ne : fourWhiteDegree G U x≠2 := fun h => yes ⟨outside,h⟩
      rw [if_neg yes];unfold cubicBlueWeight;split_ifs <;> omega
  have lower := four_sum_mono Uᶜ _ _ (fun x hx => (eq x hx).le)
  have upper := four_sum_mono Uᶜ _ _ (fun x hx => (eq x hx).ge)
  have same := le_antisymm lower upper
  rw [four_sum_add] at same
  have flags : fourLabelSum Uᶜ (fun x => if x∈B then 1 else 0)=B.ncard := by
    unfold fourLabelSum
    rw [Finset.sum_boole,Nat.cast_id]
    trans B.toFinset.card
    · apply congrArg Finset.card
      ext x;simp only [Set.mem_toFinset,Finset.mem_filter]
      exact ⟨fun h => h.2,fun h => ⟨h.1,h⟩⟩
    · rw [Set.toFinset_card,←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  rw [flags,four_sum_cross,crossCount_swap] at same
  have sum (x:X) : fourWhiteDegree G U x+fourWhiteDegree G Uᶜ x=3 := by
    have part := four_degree_split G U Uᶜ disjoint_compl_right x
    rw [Set.union_compl_self] at part
    have all : fourWhiteDegree G Set.univ x=3 := by unfold fourWhiteDegree;rw [Set.inter_univ,←Nat.card_coe_set_eq,reg]
    omega
  have eqsum := four_sum_mono U _ _ (fun x _ => (sum x).le)
  have eqsum' := four_sum_mono U _ _ (fun x _ => (sum x).ge)
  have all := le_antisymm eqsum eqsum'
  rw [four_sum_add,four_sum_cross G U Uᶜ,four_sum_const] at all
  unfold cubicGroupPotential CubicPairFamily.residualCost
  change (P.active U).card=B.ncard at count
  omega

#print axioms cubic_terminal_pairs
#print axioms cubic_terminal_cost_identity
end JSP452Audit.StarHost
