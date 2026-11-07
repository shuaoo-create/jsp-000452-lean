import ActualSevenCliquePalettes
namespace JSP452Audit.StarHost
open SimpleGraph

private theorem seven_order_bound {I:Type} [Fintype I] (C:SimpleGraph (Fin 7))
    (n:I→ℕ) (copy:(forest n).IsContained C) (y:ℕ) (pos:0<y) :
    headTally n y*(y+1)≤7 := by
  have order := copy_threshold_supported_order C Set.univ (fun _ _ _ => Set.mem_univ _) n y pos copy
  simpa using order

theorem seven_profile_three {C:SimpleGraph (Fin 7)} (P:SimpleGraph (Vertices sevenStarLeaves)) (a:ℕ)
    (heads : 5≤a ∨ ∀v,Nat.card (C.neighborSet v)≤a)
    (fit : fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) a 2 1) :
    PreservesSmallForests C P 5 := by
  intro I fin n pos small copy
  have first : ∀i,n i≤a := by rcases heads with big|cap;exact fun i => (small i).trans big;exact copied_head_degree_cap C n copy a cap
  have one := seven_order_bound C n copy 3 (by decide)
  have two := seven_order_bound C n copy 2 (by decide)
  have three := seven_order_bound C n copy 1 (by decide)
  rw [head_tally_one n pos] at three
  exact copy_from_three_thresholds n P a 2 1 first (by change headTally n 3≤1;omega) (by change headTally n 2≤2;omega) (by omega) fit

theorem seven_five_profiles (P Q : SimpleGraph (Vertices sevenStarLeaves))
    (fst : fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) 4 1 0)
    (snd : fitsThree (fun i => Nat.card (Colored sevenStarLeaves Q i)) 5 2 0) :
    PreservesSmallForests sevenFive P 5 ∧ PreservesSmallForests (sevenComplete \ sevenFive) Q 5 := by
  obtain ⟨S,order,support,cover⟩ := seven_five_support
  constructor
  · intro I fin n pos small copy
    have first (i:I) : n i≤4 := by
      have inc := copy_threshold_supported_order sevenFive S support n (n i) (pos i) copy
      have present : 0<headTally n (n i) := Finset.card_pos.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_rfl⟩⟩
      have unit := Nat.mul_le_mul_right (n i+1) (show 1≤headTally n (n i) from present)
      rw [one_mul] at unit
      omega
    have one := copy_threshold_supported_order sevenFive S support n 2 (by decide) copy
    have two := copy_threshold_supported_order sevenFive S support n 1 (by decide) copy
    have cnt := head_tally_one n pos
    exact copy_from_three_thresholds n P 4 1 0 first (by change headTally n 2≤1;omega) (by change headTally n 1≤2;omega) (by omega) fst
  · intro I fin n pos small copy
    have one := seven_order_bound (sevenComplete \ sevenFive) n copy 3 (by decide)
    have rank := matchingEdges_le_cover_card (sevenComplete \ sevenFive) Sᶜ cover
    have two := (forest_copy_matching _ n pos copy).trans rank
    have total := Set.ncard_add_ncard_compl S
    rw [Nat.card_fin] at total
    have cnt := head_tally_one n pos
    exact copy_from_three_thresholds n Q 5 2 0 small (by change headTally n 3≤1;omega) (by change headTally n 1≤2;omega) (by omega) snd

#print axioms seven_profile_three
#print axioms seven_five_profiles
end JSP452Audit.StarHost
