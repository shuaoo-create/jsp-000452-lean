import HallNeighborhoods

namespace JSP452Audit.StarHost

variable {R C : Type*} [Finite R] [Finite C]

/-- Maximum exact nonnegative Hall deficiency inside H. The empty subset
attains zero even if every nonempty candidate has more neighbors than elements. -/
noncomputable def classDeficiency {A B : Type*} [Finite A] [Finite B] (L : A → B → Prop)
    (H : Set B) : ℕ := by
  classical
  exact Nat.findGreatest (fun h => ∃ T : Set B, T ⊆ H ∧ T.ncard = (rootNeighbors L T).ncard+h) H.ncard

theorem class_deficiency_bounds (L : R → C → Prop) (H : Set C) :
    (∀ T ⊆ H, T.ncard ≤ (rootNeighbors L T).ncard+classDeficiency L H) ∧
      (∃ T ⊆ H, T.ncard = (rootNeighbors L T).ncard+classDeficiency L H) := by
  classical
  let P (h : ℕ) := ∃ T : Set C, T ⊆ H ∧ T.ncard = (rootNeighbors L T).ncard+h
  have zero : P 0 := ⟨∅,Set.empty_subset _,by rw [rootNeighbors_empty,Set.ncard_empty,Set.ncard_empty]⟩
  change (∀ T ⊆ H, T.ncard ≤ (rootNeighbors L T).ncard+Nat.findGreatest P H.ncard) ∧
    P (Nat.findGreatest P H.ncard)
  refine ⟨?_,Nat.findGreatest_spec (Nat.zero_le _) zero⟩
  intro T included
  by_cases need : (rootNeighbors L T).ncard ≤ T.ncard
  · have sub := Set.ncard_le_ncard included
    have witness : P (T.ncard-(rootNeighbors L T).ncard) := ⟨T,included,by omega⟩
    have upper := Nat.le_findGreatest (n := H.ncard) (by omega) witness
    omega
  · omega

theorem class_deficiency_attained (L : R → C → Prop) (H : Set C) :
    ∃ h : ℕ, (∀ T ⊆ H, T.ncard ≤ (rootNeighbors L T).ncard+h) ∧
      (∃ T ⊆ H, T.ncard = (rootNeighbors L T).ncard+h) :=
  ⟨classDeficiency L H,class_deficiency_bounds L H⟩

/-- Assigned components of T have different incident roots in its neighborhood;
all other components of T are among the unassigned members of H. -/
theorem class_deficit_le_free (L : R → C → Prop) (H : Set C) (place : R ↪ C)
    (respects : ∀ a, L a (place a)) (T : Set C) (included : T ⊆ H) :
    T.ncard ≤ (rootNeighbors L T).ncard + (H \ Set.range place).ncard := by
  classical
  let A := Set.range place ∩ T
  have source (c : A) : ∃ a : R, place a = c.val := c.property.1
  choose root hits using source
  let f (c : A) : rootNeighbors L T :=
    ⟨root c,c.val,c.property.2,hits c ▸ respects (root c)⟩
  have inj : Function.Injective f := by
    intro a b same
    have eq : root a = root b := congrArg Subtype.val same
    exact Subtype.ext ((hits a).symm.trans ((congrArg place eq).trans (hits b)))
  have charged : A.ncard ≤ (rootNeighbors L T).ncard := Nat.card_le_card_of_injective f inj
  have remaining := Set.ncard_le_ncard (show T \ Set.range place ⊆ H \ Set.range place from
    fun x h => ⟨included h.1,h.2⟩)
  have split := Set.ncard_sdiff_add_ncard_of_subset (show A ⊆ T from Set.inter_subset_right)
  change (T \ (Set.range place ∩ T)).ncard + A.ncard = T.ncard at split
  rw [Set.sdiff_inter_self_eq_sdiff] at split
  omega

theorem classDeficiency_le_free (L : R → C → Prop) (H : Set C) (place : R ↪ C)
    (respects : ∀ a, L a (place a)) : classDeficiency L H ≤ (H \ Set.range place).ncard := by
  obtain ⟨T,included,equal⟩ := (class_deficiency_bounds L H).2
  have := class_deficit_le_free L H place respects T included
  omega

#print axioms class_deficiency_attained
#print axioms class_deficit_le_free
#print axioms classDeficiency_le_free
end JSP452Audit.StarHost
