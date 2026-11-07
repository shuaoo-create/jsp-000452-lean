import SevenPalettesPreserveWholeForests
namespace JSP452Audit.StarHost
open SimpleGraph

private def sevenPair (P Q:SimpleGraph (Vertices sevenStarLeaves)) : Prop :=
  ∃A:SimpleGraph (Fin 7),A≤sevenComplete ∧ PreservesSmallForests A P 5 ∧
    PreservesSmallForests (sevenComplete \ A) Q 5

private theorem swap_seven_pair {P Q:SimpleGraph (Vertices sevenStarLeaves)} (pair:sevenPair P Q) : sevenPair Q P := by
  obtain ⟨A,cap,red,blue⟩ := pair
  have invol : sevenComplete \ (sevenComplete \ A)=A := by
    ext x y
    change (sevenComplete.Adj x y ∧ ¬(sevenComplete.Adj x y ∧ ¬A.Adj x y)) ↔ A.Adj x y
    have sub : A.Adj x y → sevenComplete.Adj x y := fun e => cap e
    tauto
  exact ⟨_,sdiff_le,blue,by rw [invol];exact red⟩

private theorem mono_seven_pair (P Q:SimpleGraph (Vertices sevenStarLeaves))
    (fit:fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) 5 2 1) : sevenPair P Q := by
  refine ⟨sevenComplete,le_rfl,seven_profile_three P 5 (Or.inl le_rfl) fit,?_⟩
  rw [sdiff_self]
  exact bottom_forest_preserves Q 5

private theorem five_seven_pair (P Q:SimpleGraph (Vertices sevenStarLeaves))
    (fst:fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) 4 1 0)
    (snd:fitsThree (fun i => Nat.card (Colored sevenStarLeaves Q i)) 5 2 0) : sevenPair P Q := by
  obtain ⟨red,blue⟩ := seven_five_profiles P Q fst snd
  exact ⟨sevenFive,le_top,red,blue⟩

private theorem cycle_seven_pair (P Q:SimpleGraph (Vertices sevenStarLeaves))
    (fst:fitsThree (fun i => Nat.card (Colored sevenStarLeaves P i)) 4 2 1)
    (snd:fitsThree (fun i => Nat.card (Colored sevenStarLeaves Q i)) 2 2 1) : sevenPair P Q := by
  apply swap_seven_pair
  exact ⟨sevenCycle,le_top,seven_profile_three Q 2 (Or.inr seven_cycle_caps.1) snd,
    seven_profile_three P 4 (Or.inr seven_cycle_caps.2) fst⟩

theorem seven_clique_simulated_at_five : SimulatesSmallForests sevenComplete (forest sevenStarLeaves) 5 := by
  intro P _
  let Q := forest sevenStarLeaves \ P
  change sevenPair P Q
  rcases four_star_actual_menu P with first|second|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩|⟨a,b⟩
  · exact mono_seven_pair P Q first
  · exact swap_seven_pair (mono_seven_pair Q P second)
  · exact five_seven_pair P Q a b
  · exact swap_seven_pair (five_seven_pair Q P a b)
  · exact cycle_seven_pair P Q a b
  · exact swap_seven_pair (cycle_seven_pair Q P a b)

#print axioms seven_clique_simulated_at_five
end JSP452Audit.StarHost
