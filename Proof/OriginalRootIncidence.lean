import OriginalThreePathShape
import CrossingBoundaryBudget
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem uniform_cross_count (Q : SimpleGraph X) (A I : Set X) (k : ℕ)
    (uniform : ∀x∈A,(Q.neighborSet x∩I).ncard=k) : crossCount Q I A=A.ncard*k := by
  classical
  let _ := Fintype.ofFinite A
  rw [crossCount_swap,crossCount_eq_neighbor_sum]
  calc
    _ = ∑ _ : A,k := Finset.sum_congr rfl (fun v _ => uniform v.val v.property)
    _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]

theorem degree_to_root_and_residual (Q : SimpleGraph X) (I : Set X) (v : ↥(Iᶜ : Set X)) :
    (Q.neighborSet v.val∩I).ncard+Nat.card ((Q.induce Iᶜ).neighborSet v)=Nat.card (Q.neighborSet v.val) := by
  let N := Q.neighborSet v.val
  rw [induced_degree_intersection,Nat.card_coe_set_eq]
  have dis : Disjoint (N∩I) (N∩Iᶜ) := disjoint_compl_right.mono Set.inter_subset_right Set.inter_subset_right
  change (N∩I).ncard+(N∩Iᶜ).ncard=N.ncard
  rw [←Set.ncard_union_eq dis,←Set.inter_union_distrib_left,Set.union_compl_self,Set.inter_univ]

/-- The original roots can send at most D+1 edges to the large companion
clique. Every singleton sends D to the roots, and each leaf sends D−1. -/
theorem three_path_companion_root_cap (Q : SimpleGraph X) (I : Set X)
    (ind : Q.IsIndepSet I) (largest : ∀A : Set X,Q.IsIndepSet A → A.ncard≤I.ncard)
    (D : ℕ) (large : 6≤D) (reg : ∀v,Nat.card (Q.neighborSet v)=D)
    (s : ThreePathShape (Q.induce Iᶜ) D) (count : s.singles.ncard+3=I.ncard) :
    crossCount Q I (Subtype.val '' s.companion)≤D+1 := by
  classical
  let U : Fin 5 → Set ↥(Iᶜ : Set X) := fun i => if i=0 then s.singles else if i=1 then {s.left} else if i=2 then {s.right} else if i=3 then {s.pivot} else s.companion
  let C (i:Fin 5) : Set X := Subtype.val '' U i
  have lf := s.path_free s.left (by simp)
  have rf := s.path_free s.right (by simp)
  have pf := s.path_free s.pivot (by simp)
  have pairwiseDis : ∀i j,i≠j → Disjoint (U i) (U j) := by
    intro i j ne
    fin_cases i <;> fin_cases j <;>
      simp_all [U,s.different,Ne.symm s.different,s.left_off,Ne.symm s.left_off,
        s.right_off,Ne.symm s.right_off,s.clean,s.clean.symm]
  have bound := sum_cross_into_disjoint Q I Set.univ C (fun _ => Set.subset_univ _)
    (fun i j ne => Set.disjoint_image_of_injective Subtype.val_injective (pairwiseDis i j ne))
  have all : crossCount Q I Set.univ=I.ncard*D := by
    let _ := Fintype.ofFinite I
    rw [crossCount_eq_neighbor_sum]
    calc
      _ = ∑ _ : I,D := Finset.sum_congr rfl (fun v _ => by
        rw [Set.inter_univ,←Nat.card_coe_set_eq,reg])
      _ = _ := by simp [←Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
  have fromSingles : crossCount Q I (C 0)=s.singles.ncard*D := by
    have uni (v:X) (hv:v∈C 0) : (Q.neighborSet v∩I).ncard=D := by
      obtain ⟨z,hz,rfl⟩ := hv
      have empty : (Q.induce Iᶜ).neighborSet z=∅ := Set.eq_empty_iff_forall_notMem.mpr (s.isolated z hz)
      have eq := degree_to_root_and_residual Q I z
      rw [empty,Nat.card_coe_set_eq,Set.ncard_empty,add_zero,reg] at eq;exact eq
    rw [uniform_cross_count Q (C 0) I D uni]
    rw [show (C 0).ncard=s.singles.ncard from Set.ncard_image_of_injective _ Subtype.val_injective]
  have leafPrice (v : ↥(Iᶜ : Set X)) (hv : (Q.induce Iᶜ).neighborSet v={s.pivot}) :
      crossCount Q I (Subtype.val '' ({v} : Set ↥(Iᶜ : Set X)))=D-1 := by
    have eq := degree_to_root_and_residual Q I v
    rw [hv,Nat.card_coe_set_eq,Set.ncard_singleton,reg] at eq
    have h := uniform_cross_count Q (Subtype.val '' ({v} : Set ↥(Iᶜ : Set X))) I (D-1) (by
      rintro _ ⟨z,hz,rfl⟩
      have same := Set.mem_singleton_iff.mp hz
      subst z;omega)
    simpa using h
  have leftPrice : crossCount Q I (C 1)=D-1 := leafPrice s.left s.left_neighbors
  have rightPrice : crossCount Q I (C 2)=D-1 := leafPrice s.right s.right_neighbors
  have pivotPos : 1≤crossCount Q I (C 3) := by
    let N := Q.neighborSet s.pivot.val∩I
    obtain ⟨z,zi,edge⟩ := largest_independent_dominates Q I ind largest s.pivot.val s.pivot.property
    have ne := (Set.ncard_pos (Set.toFinite N)).mpr (show N.Nonempty from ⟨z,edge,zi⟩)
    have h := uniform_cross_count Q (Subtype.val '' ({s.pivot} : Set ↥(Iᶜ : Set X))) I N.ncard (by
      rintro _ ⟨v,hv,rfl⟩;rw [Set.mem_singleton_iff.mp hv])
    change 1≤crossCount Q I (Subtype.val '' ({s.pivot} : Set ↥(Iᶜ : Set X)))
    have hh : crossCount Q I (Subtype.val '' ({s.pivot} : Set ↥(Iᶜ : Set X)))=N.ncard := by simpa using h
    rw [hh];exact ne
  rw [all,←count,Nat.add_mul] at bound
  have expand (f : Fin 5→ℕ) : (∑i,f i)=f 0+(f 1+(f 2+(f 3+f 4))) := by
    rw [show (Finset.univ : Finset (Fin 5))={0,1,2,3,4} by decide]
    simp
  rw [expand] at bound
  rw [fromSingles,leftPrice,rightPrice] at bound
  change crossCount Q I (C 4)≤D+1
  omega

#print axioms three_path_companion_root_cap
end JSP452Audit.StarHost
