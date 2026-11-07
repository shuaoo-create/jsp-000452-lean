import FailureNormalization
import ExposeRestrict
namespace JSP452Audit.StarHost
open SimpleGraph
/-- The finite suffix of the original positive profile, with no values beyond its domain. -/
abbrev originalTail {s : ℕ} (n : Fin s → ℕ) (i : Fin s) (k : Fin (s-i.val)) : ℕ :=
  padDemand n (i.val+k.val)

/-- Number of stars in the suffix at least as large as its head. -/
def headWidth {s : ℕ} (n : Fin s → ℕ) (i : Fin s) : ℕ :=
  (Finset.univ.filter (fun k : Fin (s-i.val) => n i ≤ originalTail n i k)).card

theorem headWidth_pos {s : ℕ} (n : Fin s → ℕ) (i : Fin s) : 0 < headWidth n i := by
  apply Finset.card_pos.mpr
  let k : Fin (s-i.val) := ⟨0,by have := i.isLt; omega⟩
  exact ⟨k,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simp [originalTail,k,padDemand,i.isLt]⟩⟩

theorem forces_original_tails {X : Type*} (G : SimpleGraph X) {s t r : ℕ}
    (n : Fin s → ℕ) (m : Fin t → ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (i : Fin s) (j : Fin t) (idx : i.val+j.val=r) :
    Forces G (forest (originalTail n i)) (forest (originalTail m j)) :=
  row _ _ _ _ idx (by have := i.isLt; omega) (by have := j.isLt; omega)
    (by have := i.isLt; omega) (by have := j.isLt; omega)

/-- A control set strictly smaller than the sum of the two positive thresholds minus one
splits into two disjoint parts, each strictly smaller than its own threshold. -/
theorem split_control_budget {X : Type*} [Finite X] (W : Set X) {u v : ℕ}
    (hu : 0<u) (hv : 0<v) (small : W.ncard < u+v-1) :
    ∃ A B : Set X, A ∪ B = W ∧ Disjoint A B ∧ A.ncard < u ∧ B.ncard < v := by
  classical
  let F := W.toFinite.toFinset
  have eqF : (F : Set X) = W := W.toFinite.coe_toFinset
  have cardF : F.card = W.ncard := by rw [← eqF, Set.ncard_coe_finset]
  obtain ⟨A,sub,size⟩ := Finset.exists_subset_card_eq (show min (u-1) F.card ≤ F.card from min_le_right _ _)
  refine ⟨(A : Set X),(↑(F \ A) : Set X),?_,?_,?_,?_⟩
  · rw [← eqF,← Finset.coe_union]
    congr 1
    ext x
    simp only [Finset.mem_union,Finset.mem_sdiff]
    constructor
    · rintro (h|h); exact sub h; exact h.1
    · intro h
      by_cases ha : x∈A
      · exact Or.inl ha
      · exact Or.inr ⟨h,ha⟩
  · exact Set.disjoint_left.mpr (fun _ hA hB => (Finset.mem_sdiff.mp hB).2 hA)
  · rw [Set.ncard_coe_finset,size]; omega
  · rw [Set.ncard_coe_finset,Finset.card_sdiff_of_subset sub,size]; omega

#print axioms split_control_budget
#print axioms forces_original_tails
#print axioms headWidth_pos
end JSP452Audit.StarHost