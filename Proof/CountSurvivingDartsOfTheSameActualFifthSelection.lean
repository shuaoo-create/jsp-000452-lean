import CountActualFifthSelectionsOnSingletonsAndClosedNeighborhoods
open private JSP452Audit.StarHost.sum_incidence_counts from QuarterSampleTransversal
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem dart_count_on_actual_labels {V:Type u} [Finite V] (C:SimpleGraph V) :
    Nat.card C.Dart=2*C.edgeSet.ncard := by
  classical
  let _ := Fintype.ofFinite V
  rw [Nat.card_eq_fintype_card,C.dart_card_eq_twice_card_edges]
  simp [Set.ncard_eq_toFinset_card',SimpleGraph.edgeFinset]

theorem induced_darts_on_surviving_labels {V:Type u} [Finite V] (C:SimpleGraph V) (A:Set V) :
    2*(C.induce Aᶜ).edgeSet.ncard=({d:C.Dart | d.fst∉A ∧ d.snd∉A}:Set C.Dart).ncard := by
  classical
  let eqv : (C.induce Aᶜ).Dart ≃ ↥({d:C.Dart | d.fst∉A ∧ d.snd∉A}:Set C.Dart) := {
    toFun := fun d => ⟨⟨(d.fst.val,d.snd.val),d.adj⟩,d.fst.property,d.snd.property⟩
    invFun := fun d => ⟨(⟨d.val.fst,d.property.1⟩,⟨d.val.snd,d.property.2⟩),d.val.adj⟩
    left_inv := by intro d;rfl
    right_inv := by intro d;rfl }
  rw [←dart_count_on_actual_labels,Nat.card_congr eqv,Nat.card_coe_set_eq]

noncomputable def fifthChosen {V:Type*} (f:V→Fin 5) : Set V := {v | f v=0}

theorem fifth_surviving_darts_total {V:Type u} [Fintype V] [DecidableEq V] (C:SimpleGraph V) :
    (∑f:V→Fin 5,((2*(C.induce (fifthChosen f)ᶜ).edgeSet.ncard:ℕ):ℚ))=
      (5:ℚ)^(Nat.card V)*(16/25)*(2*C.edgeSet.ncard) := by
  classical
  let _ := Fintype.ofFinite C.Dart
  let L := V→Fin 5
  have total := JSP452Audit.StarHost.sum_incidence_counts (fun (f:L) (d:C.Dart) => d.fst∉fifthChosen f ∧ d.snd∉fifthChosen f)
  have term (d:C.Dart) :
      (Nat.card {f:L // d.fst∉fifthChosen f ∧ d.snd∉fifthChosen f}:ℚ)=(5:ℚ)^(Nat.card V)*(16/25) := by
    have both := missed_fifth_weight ({d.fst,d.snd}:Set V)
    rw [Set.ncard_pair d.fst_ne_snd] at both
    have eq : {f:L | ∀v∈({d.fst,d.snd}:Set V),f v≠0}={f | d.fst∉fifthChosen f ∧ d.snd∉fifthChosen f} := by
      ext f
      change (∀v∈({d.fst,d.snd}:Set V),f v≠0) ↔ f d.fst≠0 ∧ f d.snd≠0
      simp
    change (Nat.card ↥({f:L | ∀v∈({d.fst,d.snd}:Set V),f v≠0}:Set L):ℚ)=_ at both
    rw [eq] at both
    rw [show (4/5:ℚ)^2=16/25 by norm_num] at both
    exact both
  simp_rw [induced_darts_on_surviving_labels]
  have eq : (∑f:L,(({d:C.Dart | d.fst∉fifthChosen f ∧ d.snd∉fifthChosen f}:Set C.Dart).ncard:ℚ))=
      ∑d:C.Dart,(Nat.card {f:L // d.fst∉fifthChosen f ∧ d.snd∉fifthChosen f}:ℚ) := by exact_mod_cast total
  rw [eq,Finset.sum_congr rfl (fun d _ => term d),Finset.sum_const,Finset.card_univ,nsmul_eq_mul,←Nat.card_eq_fintype_card,dart_count_on_actual_labels]
  push_cast;ring

#print axioms dart_count_on_actual_labels
#print axioms induced_darts_on_surviving_labels
#print axioms fifth_surviving_darts_total
end JSP452Audit.StarHost