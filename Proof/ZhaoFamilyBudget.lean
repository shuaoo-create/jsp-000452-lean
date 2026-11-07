import ZhaoFamilyStructure
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem cut_neighbor_account {X : Type*} [Finite X] (G : SimpleGraph X)
    (U : Set X) (x : ↥Uᶜ) :
    Nat.card ((G.induce Uᶜ).neighborSet x) + (G.neighborSet x.val ∩ U).ncard =
      Nat.card (G.neighborSet x.val) := by
  let e : ((G.induce Uᶜ).neighborSet x) ≃ ↥(G.neighborSet x.val \ U) := {
    toFun := fun y => ⟨y.val.val,y.property,y.val.property⟩
    invFun := fun y => ⟨⟨y.val,y.property.2⟩,y.property.1⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  rw [Nat.card_congr e,Nat.card_coe_set_eq,Nat.card_coe_set_eq]
  have total := Set.ncard_sdiff_add_ncard_of_subset (s := G.neighborSet x.val ∩ U)
    (t := G.neighborSet x.val) Set.inter_subset_left
  have setEq : G.neighborSet x.val \ (G.neighborSet x.val ∩ U) = G.neighborSet x.val \ U := by
    ext; simp only [Set.mem_sdiff,Set.mem_inter_iff]; tauto
  rwa [setEq] at total

/-- A one-step cyclic shift, also for finite types of order zero or one. -/
private def cycleShift (n : ℕ) : Equiv.Perm (Fin n) where
  toFun i := ⟨if i.val+1 < n then i.val+1 else 0,by have := i.isLt; split <;> omega⟩
  invFun i := ⟨if i.val=0 then n-1 else i.val-1,by have := i.isLt; split <;> omega⟩
  left_inv i := by
    apply Fin.ext
    by_cases step : i.val+1<n
    · simp [step]
    · simp [step]
      have := i.isLt
      omega
  right_inv i := by apply Fin.ext; have := i.isLt; dsimp; split_ifs <;> omega

private theorem cyclic_shift_ne {n : ℕ} (large : 2 ≤ n) (i : Fin n) : i ≠ cycleShift n i := by
  intro eq
  have vals := congrArg Fin.val eq
  change i.val = (if i.val+1<n then i.val+1 else 0) at vals
  split at vals <;> omega

/-- Delete the two zero labels. The center loses both; each surviving old label
loses the opposite zero and is paired across parts via cyclic shift. -/
theorem zhao_budget_of_regular (d : ℕ) (hd : 2 ≤ d)
    (reg : ∀ x, Nat.card ((zhaoGraph d).neighborSet x) = 2*d) :
    deletionBudget (zhaoGraph d) (2*d-1) ≤ 2 := by
  classical
  let I := Fin (2*d-1)
  let o : Fin (2*d) := ⟨0,by omega⟩
  let tag (i : I) : Fin (2*d) := ⟨i.val+1,by have := i.isLt; dsimp [I] at i; omega⟩
  have inject : Function.Injective tag := fun i j eq => Fin.ext (by
    have h : i.val+1=j.val+1 := congrArg Fin.val eq; omega)
  have nonzero (i : I) : tag i ≠ o := by intro eq; have h : i.val+1=0 := congrArg Fin.val eq; omega
  have onto (v : Fin (2*d)) (hv : v≠o) : ∃ i, tag i=v := by
    have pos : 0<v.val := Nat.pos_of_ne_zero (fun h => hv (Fin.ext h))
    exact ⟨⟨v.val-1,by have := v.isLt; omega⟩,Fin.ext (by dsimp [tag]; omega)⟩
  let U : Set (ZhaoVertex d) := {zhaoLeft o,zhaoRight o}
  let H := (zhaoGraph d).induce Uᶜ
  let L : I ↪ ↥Uᶜ := {
    toFun := fun i => ⟨zhaoLeft (tag i),by simp [U,zhaoLeft,zhaoRight,nonzero]⟩
    inj' := by intro i j eq; apply inject; simpa [zhaoLeft] using congrArg Subtype.val eq }
  let R : I ↪ ↥Uᶜ := {
    toFun := fun i => ⟨zhaoRight (tag (cycleShift _ i)),by simp [U,zhaoLeft,zhaoRight,nonzero]⟩
    inj' := by
      intro i j eq; apply (cycleShift _).injective; apply inject
      simpa [zhaoRight] using congrArg Subtype.val eq }
  have edges (i : I) : H.Adj (L i) (R i) :=
    Or.inl (fun eq => cyclic_shift_ne (by dsimp [I] at i; omega) i (inject eq))
  have apart : Disjoint (Set.range L) (Set.range R) := by
    apply Set.disjoint_left.mpr
    rintro _ ⟨i,rfl⟩ ⟨j,eq⟩
    have h := congrArg Subtype.val eq
    simp [L,R,zhaoLeft,zhaoRight] at h
  let M := Padded.pairFamily H L R edges
  have hm := Padded.pairFamily_isMatching H L R edges apart
  have zeroL : zhaoLeft o ∈ U := Or.inl rfl
  have zeroR : zhaoRight o ∈ U := Or.inr rfl
  have cutCard : U.ncard=2 := Set.ncard_pair (by simp [zhaoLeft,zhaoRight])
  have centerLoss (x : ↥Uᶜ) (center : x.val=none) : Nat.card (H.neighborSet x) ≤ 2*d-2 := by
    have loss := cut_neighbor_account (zhaoGraph d) U x
    have all : U ⊆ (zhaoGraph d).neighborSet x.val := by
      rintro y (hl|hr)
      · subst y; rw [center]; change o.val<d; dsimp [o]; omega
      · obtain rfl := Set.mem_singleton_iff.mp hr; rw [center]; change o.val<d; dsimp [o]; omega
    rw [Set.inter_eq_right.mpr all,cutCard,reg] at loss
    change Nat.card (((zhaoGraph d).induce Uᶜ).neighborSet x) ≤ 2*d-2
    omega
  have labelLoss (x : ↥Uᶜ) (lossOne : ((zhaoGraph d).neighborSet x.val ∩ U).Nonempty) :
      Nat.card (H.neighborSet x) ≤ 2*d-1 := by
    have ind := cut_neighbor_account (zhaoGraph d) U x
    have h := (Set.ncard_pos (s := _)).mpr lossOne
    rw [reg] at ind
    change Nat.card (((zhaoGraph d).induce Uᶜ).neighborSet x) ≤ 2*d-1
    omega
  have classified (x : ↥Uᶜ) : x.val = none ∨
      (Nat.card (H.neighborSet x) ≤ 2*d-1 ∧ x ∈ M.verts) := by
    rcases x with ⟨_ | ⟨v|v⟩,surv⟩
    · exact Or.inl rfl
    · have nz : v ≠ o := fun eq => surv (eq ▸ zeroL)
      obtain ⟨i,rfl⟩ := onto v nz
      exact Or.inr ⟨labelLoss _ ⟨zhaoRight o,Or.inl (nonzero i),zeroR⟩,Or.inl ⟨i,rfl⟩⟩
    · have nz : v ≠ o := fun eq => surv (eq ▸ zeroR)
      obtain ⟨i,rfl⟩ := onto v nz
      refine Or.inr ⟨labelLoss _ ⟨zhaoLeft o, Or.inl (nonzero i).symm,zeroL⟩, Or.inr ?_⟩
      exact ⟨(cycleShift _).symm i,Subtype.ext (congrArg (fun t => zhaoRight (tag t)) ((cycleShift _).apply_symm_apply i))⟩
  apply (deletionBudget_le_of_witness (zhaoGraph d) (2*d-1) U ?_).trans_eq cutCard
  apply admits_remainder_of_full_cover H (2*d-1) (by omega) ?_ M hm ?_
  · intro x; rcases classified x with h|h
    · have := centerLoss x h; omega
    · exact h.1
  · intro x full; rcases classified x with h|h
    · have := centerLoss x h; omega
    · exact h.2

theorem zhao_family_budget (d : ℕ) (hd : 2 ≤ d) :
    deletionBudget (zhaoGraph d) (2*d-1) ≤ 2 :=
  zhao_budget_of_regular d hd (zhao_regular d)

#print axioms zhao_budget_of_regular
#print axioms zhao_family_budget
end JSP452Audit.StarHost
