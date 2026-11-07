import MaximalBarrier
import NestedBarrier
import ParityGap

namespace JSP452Audit.StarHost
open SimpleGraph JSP452Audit.Padded
variable {X : Type*} [Finite X]

/-- A further deletion can create at most one additional uncovered vertex
per deleted original label. Pull an attained cut of the residual back to G. -/
theorem minUnmatched_after_cut_le (G : SimpleGraph X) (A : Set X) :
    minUnmatched (G.induce Aᶜ) ≤ minUnmatched G + A.ncard := by
  obtain ⟨W,attained⟩ := tutte_berge_attained (G.induce Aᶜ)
  have upper := tutte_berge_upper_all G (outerCut A W)
  rw [← odd_ncard_iso (nestedCutIso G A W),attained,outerCut_ncard] at upper
  omega

/-- Arbitrary deletion loses at most the number of deleted vertices in matching rank. -/
theorem matching_rank_le_cut_add (G : SimpleGraph X) (A : Set X) :
    matchingEdges G ≤ A.ncard + matchingEdges (G.induce Aᶜ) := by
  have deficit := minUnmatched_after_cut_le G A
  have host := minUnmatched_add_twice_matching G
  have residual := minUnmatched_add_twice_matching (G.induce Aᶜ)
  rw [Nat.card_coe_set_eq] at residual
  have count := Set.ncard_add_ncard_compl A
  omega

/-- The residual deficiency increases by exactly the number deleted when the
deleted vertices belong to a tight barrier. No component structure is assumed. -/
theorem tight_deletes_deficit (G : SimpleGraph X) (S A : Set X)
    (tight : IsTightBarrier G S) (sub : A ⊆ S) :
    minUnmatched (G.induce Aᶜ) = minUnmatched G + A.ncard := by
  let W : Set ↥(Aᶜ : Set X) := {x | x.val ∈ S}
  have join : outerCut A W = S := by
    ext v
    constructor
    · rintro (ha | ⟨w,hw,rfl⟩)
      · exact sub ha
      · exact hw
    · intro hs
      by_cases ha : v ∈ A
      · exact Or.inl ha
      · exact Or.inr ⟨⟨v,ha⟩,hs,rfl⟩
  have count := outerCut_ncard A W
  rw [join] at count
  have upper := tutte_berge_upper_all (G.induce Aᶜ) W
  rw [odd_ncard_iso (nestedCutIso G A W),join] at upper
  change (G.induce Sᶜ).oddComponents.ncard = S.ncard + minUnmatched G at tight
  have other := minUnmatched_after_cut_le G A
  omega

theorem tight_deletes_rank (G : SimpleGraph X) (S A : Set X)
    (tight : IsTightBarrier G S) (sub : A ⊆ S) :
    matchingEdges G = A.ncard + matchingEdges (G.induce Aᶜ) := by
  have deficit := tight_deletes_deficit G S A tight sub
  have host := minUnmatched_add_twice_matching G
  have residual := minUnmatched_add_twice_matching (G.induce Aᶜ)
  rw [Nat.card_coe_set_eq] at residual
  have count := Set.ncard_add_ncard_compl A
  omega

#print axioms minUnmatched_after_cut_le
#print axioms matching_rank_le_cut_add
#print axioms tight_deletes_deficit
#print axioms tight_deletes_rank
end JSP452Audit.StarHost
