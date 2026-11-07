import ZhaoModels

namespace JSP452Audit.StarHost
open SimpleGraph

theorem zhao_left_ncard (d : ℕ) :
    (Set.range (@zhaoLeft d)).ncard = 2*d := by
  rw [Set.ncard_range_of_injective (show Function.Injective (@zhaoLeft d) from
    fun _ _ h => Sum.inl.inj (Option.some.inj h)),Nat.card_fin]

theorem zhao_left_independent (d : ℕ) :
    (zhaoGraph d).IsIndepSet (Set.range (@zhaoLeft d)) := by
  rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩ _ h
  exact h

private theorem right_count (d : ℕ) : (Set.range (@zhaoRight d)).ncard = 2*d := by
  rw [Set.ncard_range_of_injective (show Function.Injective (@zhaoRight d) from
    fun _ _ h => Sum.inr.inj (Option.some.inj h)),Nat.card_fin]

/-- Replacing one indexed vertex by the center preserves the cardinality. -/
private theorem replace_one_card {X : Type*} [Finite X] (A : Set X) (z one : X)
    (nz : z ∉ A) (member : one ∈ A) :
    (insert z (A \ {one})).ncard = A.ncard := by
  have fresh : z ∉ A \ {one} := fun h => nz h.1
  rw [Set.ncard_insert_of_notMem fresh]
  have account := Set.ncard_sdiff_add_ncard_of_subset (Set.singleton_subset_iff.mpr member)
  rwa [Set.ncard_singleton] at account

private theorem center_degree (d : ℕ) : Nat.card ((zhaoGraph d).neighborSet none) = 2*d := by
  let up (i : Fin d) : Fin (2*d) := ⟨i.val,by have h := i.isLt; omega⟩
  let f : Fin d ⊕ Fin d → ZhaoVertex d := Sum.elim (fun i => zhaoLeft (up i)) (fun i => zhaoRight (up i))
  have injs : Function.Injective up := fun _ _ h => Fin.ext (congrArg (fun k : Fin (2*d) => k.val) h)
  have inj : Function.Injective f := by
    rintro (i|i) (j|j) h
    · exact congrArg Sum.inl (injs (Sum.inl.inj (Option.some.inj h)))
    · cases h
    · cases h
    · exact congrArg Sum.inr (injs (Sum.inr.inj (Option.some.inj h)))
  have centers : (zhaoGraph d).neighborSet none = Set.range f := by
    ext x
    constructor
    · intro adj
      rcases x with _ | ⟨i|i⟩
      · exact adj.elim
      · exact ⟨.inl ⟨i.val,adj⟩,rfl⟩
      · exact ⟨.inr ⟨i.val,adj⟩,rfl⟩
    · rintro ⟨i|i,rfl⟩ <;> exact i.isLt
  change ((zhaoGraph d).neighborSet none).ncard = 2*d
  rw [centers,Set.ncard_range_of_injective inj,Nat.card_sum,Nat.card_fin]
  omega

private theorem left_degree (d : ℕ) (i : Fin (2*d)) :
    Nat.card ((zhaoGraph d).neighborSet (zhaoLeft i)) = 2*d := by
  classical
  let R := Set.range (@zhaoRight d)
  have equation : (zhaoGraph d).neighborSet (zhaoLeft i) =
      if i.val < d then insert none (R \ {zhaoRight i}) else R := by
    ext v
    by_cases h : i.val < d
    · rw [if_pos h]
      rcases v with _ | ⟨j|j⟩ <;>
        simp [SimpleGraph.mem_neighborSet,zhaoGraph,zhaoAdj,zhaoLeft,zhaoRight,R,Set.mem_range,h,not_le.mpr h,ne_comm]
    · rw [if_neg h]
      rcases v with _ | ⟨j|j⟩ <;>
        simp [SimpleGraph.mem_neighborSet,zhaoGraph,zhaoAdj,zhaoLeft,zhaoRight,R,Set.mem_range,h,Nat.le_of_not_gt h]
  change ((zhaoGraph d).neighborSet (zhaoLeft i)).ncard = _
  rw [equation]; split_ifs
  · exact (replace_one_card R none (zhaoRight i) (by simp [R,zhaoRight]) ⟨i,rfl⟩).trans (right_count d)
  · exact right_count d

private theorem right_degree (d : ℕ) (i : Fin (2*d)) :
    Nat.card ((zhaoGraph d).neighborSet (zhaoRight i)) = 2*d := by
  classical
  let L := Set.range (@zhaoLeft d)
  have equation : (zhaoGraph d).neighborSet (zhaoRight i) =
      if i.val < d then insert none (L \ {zhaoLeft i}) else L := by
    ext v
    by_cases h : i.val < d
    · rw [if_pos h]
      rcases v with _ | ⟨j|j⟩ <;>
        simp [SimpleGraph.mem_neighborSet,zhaoGraph,zhaoAdj,zhaoLeft,zhaoRight,L,Set.mem_range,h]
      grind
    · rw [if_neg h]
      rcases v with _ | ⟨j|j⟩ <;>
        simp [SimpleGraph.mem_neighborSet,zhaoGraph,zhaoAdj,zhaoLeft,zhaoRight,L,Set.mem_range,h]
      grind
  change ((zhaoGraph d).neighborSet (zhaoRight i)).ncard = _
  rw [equation]; split_ifs
  · exact (replace_one_card L none (zhaoLeft i) (by simp [L,zhaoLeft]) ⟨i,rfl⟩).trans (zhao_left_ncard d)
  · exact zhao_left_ncard d

theorem zhao_regular (d : ℕ) (v : ZhaoVertex d) :
    Nat.card ((zhaoGraph d).neighborSet v) = 2*d := by
  rcases v with _ | ⟨i|i⟩
  · exact center_degree d
  · exact left_degree d i
  · exact right_degree d i

#print axioms zhao_left_ncard
#print axioms zhao_left_independent
#print axioms zhao_regular
end JSP452Audit.StarHost
