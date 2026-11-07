import PathCycleDissociation
import MatchingRemainderSplit

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A complete remainder admitting a level-one split has at most two surviving vertices. -/
private theorem clique_survivors {n : ℕ} (U : Set (Fin n))
    (feasible : admits_matching_remainder ((⊤ : SimpleGraph (Fin n)).induce Uᶜ) 1) :
    Uᶜ.ncard ≤ 2 := by
  classical
  obtain ⟨M, matching, rem⟩ := feasible
  have cap := (cover_of_matching_remainder _ M matching 1 (by decide) rem).1
  by_cases existsSurvivor : Uᶜ.Nonempty
  · obtain ⟨x, hx⟩ := existsSurvivor
    let v : ↥Uᶜ := ⟨x,hx⟩
    have neighbors : ((⊤ : SimpleGraph (Fin n)).induce Uᶜ).neighborSet v =
        ({v} : Set ↥Uᶜ)ᶜ := by
      ext w
      change v.val ≠ w.val ↔ w ≠ v
      exact ⟨fun h eq => h (congrArg Subtype.val eq.symm),
        fun h eq => h (Subtype.ext eq.symm)⟩
    have le := cap v
    rw [neighbors,Nat.card_coe_set_eq,Set.ncard_compl,Set.ncard_singleton,
      Nat.card_coe_set_eq] at le
    omega
  · rw [Set.not_nonempty_iff_eq_empty.mp existsSurvivor]
    simp

/-- The exact first deletion budget for every finite clique, including orders zero and one. -/
theorem complete_deletion_one (n : ℕ) :
    deletionBudget (⊤ : SimpleGraph (Fin n)) 1 = n - 2 := by
  classical
  let G := (⊤ : SimpleGraph (Fin n))
  apply Nat.le_antisymm
  · let U : Set (Fin n) := {x | 2 ≤ x.val}
    have cutCount : U.ncard ≤ n-2 := by
      let f (x : U) : Fin (n-2) := ⟨x.val.val-2, by
        have h : 2 ≤ x.val.val := x.property
        have := x.val.isLt
        omega⟩
      have inj : Function.Injective f := by
        intro x y eq
        have h : x.val.val-2 = y.val.val-2 := congrArg Fin.val eq
        have hx : 2 ≤ x.val.val := x.property
        have hy : 2 ≤ y.val.val := y.property
        exact Subtype.ext (Fin.ext (by omega))
      have bound := Nat.card_le_card_of_injective f inj
      rwa [Nat.card_coe_set_eq, Nat.card_fin] at bound
    apply (deletionBudget_le_of_witness G 1 U ?_).trans cutCount
    apply admits_one_of_unique_neighbor
    intro x y z xy xz
    have a : ¬ 2 ≤ x.val.val := x.property
    have b : ¬ 2 ≤ y.val.val := y.property
    have c : ¬ 2 ≤ z.val.val := z.property
    have xy' : x.val.val ≠ y.val.val := fun e => xy.ne (Subtype.ext (Fin.ext e))
    have xz' : x.val.val ≠ z.val.val := fun e => xz.ne (Subtype.ext (Fin.ext e))
    exact Subtype.ext (Fin.ext (by omega))
  · obtain ⟨U,feasible,att⟩ := deletionBudget_attained G 1
    have le := clique_survivors U feasible
    have all := Set.ncard_add_ncard_compl U
    rw [Nat.card_fin] at all
    change n-2 ≤ deletionBudget G 1
    omega

theorem clique_deletion_one (z : ℕ) (_hz : 2 ≤ z) :
    deletionBudget (⊤ : SimpleGraph (Fin (2*z+1))) 1 = 2*z-1 := by
  rw [complete_deletion_one]
  omega

#print axioms complete_deletion_one
#print axioms clique_deletion_one
end JSP452Audit.StarHost
