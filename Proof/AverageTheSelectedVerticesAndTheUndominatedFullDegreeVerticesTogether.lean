import CountSurvivingDartsOfTheSameActualFifthSelection
open private JSP452Audit.StarHost.sum_incidence_counts from QuarterSampleTransversal
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def fifthUndominated {V:Type u} [Finite V] (C:SimpleGraph V) (D:ℕ) (f:V→Fin 5) : Set V :=
  {v | Nat.card (C.neighborSet v)=D ∧ ∀z∈insert v (C.neighborSet v),f z≠0}

theorem fifth_selected_total {V:Type u} [Fintype V] [DecidableEq V] :
    (∑f:V→Fin 5,((fifthChosen f).ncard:ℚ))=(5:ℚ)^(Nat.card V)*((Nat.card V:ℚ)/5) := by
  classical
  let L := V→Fin 5
  have sum := JSP452Audit.StarHost.sum_incidence_counts (fun (f:L) (v:V) => f v=0)
  have cast : (∑f:L,((fifthChosen f).ncard:ℚ))=∑v:V,(Nat.card {f:L // f v=0}:ℚ) := by exact_mod_cast sum
  rw [cast,Finset.sum_congr rfl (fun (v:V) _ => selected_fifth_weight v)]
  rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul];ring

theorem fifth_undominated_total {V:Type u} [Fintype V] [DecidableEq V] (C:SimpleGraph V) (D:ℕ) :
    (∑f:V→Fin 5,((fifthUndominated C D f).ncard:ℚ))≤(5:ℚ)^(Nat.card V)*(Nat.card V)*(4/5:ℚ)^(D+1) := by
  classical
  let L := V→Fin 5
  let ok (f:L) (v:V) := Nat.card (C.neighborSet v)=D ∧ ∀z∈insert v (C.neighborSet v),f z≠0
  have total := JSP452Audit.StarHost.sum_incidence_counts ok
  have cast : (∑f:L,((fifthUndominated C D f).ncard:ℚ))=∑v:V,(Nat.card {f:L // ok f v}:ℚ) := by exact_mod_cast total
  have term (v:V) : (Nat.card {f:L // ok f v}:ℚ)≤(5:ℚ)^(Nat.card V)*(4/5:ℚ)^(D+1) := by
    by_cases full:Nat.card (C.neighborSet v)=D
    · let S := insert v (C.neighborSet v)
      have cnt : S.ncard=D+1 := by dsimp only [S];rw [Set.ncard_insert_of_notMem (show v∉C.neighborSet v from C.loopless.irrefl v),←Nat.card_coe_set_eq,full]
      have eq : {f:L | ok f v}={f:L | ∀z∈S,f z≠0} := by
        ext f;change ok f v ↔ _;simp only [ok,full,true_and];rfl
      have w := missed_fifth_weight S
      change (Nat.card ↥({f:L | ok f v}:Set L):ℚ)≤_
      rw [eq,←cnt];exact w.le
    · let _ : IsEmpty {f:L // ok f v} := ⟨fun f => full f.property.1⟩
      simp only [Nat.card_of_isEmpty,Nat.cast_zero];positivity
  rw [cast]
  calc
    _ ≤ ∑_v:V,((5:ℚ)^(Nat.card V)*(4/5:ℚ)^(D+1)) := Finset.sum_le_sum (fun v _ => term v)
    _ = _ := by rw [Finset.sum_const,Finset.card_univ,←Nat.card_eq_fintype_card,nsmul_eq_mul];ring

#print axioms fifth_selected_total
#print axioms fifth_undominated_total
end JSP452Audit.StarHost