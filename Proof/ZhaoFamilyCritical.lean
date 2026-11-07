import ZhaoFamilyStructure
import MaximalUncovered
import PairFamily

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X I : Type*}

/-- A family of disjoint actual pairs covering precisely all labels except v. -/
private theorem perfect_except_by_pairs (G : SimpleGraph X) (v : X) (l r : I ↪ X)
    (edges : ∀ i, G.Adj (l i) (r i)) (dis : Disjoint (Set.range l) (Set.range r))
    (support : Set.range l ∪ Set.range r = {x | x ≠ v}) :
    ∃ M : (G.induce {x | x ≠ v}).Subgraph, M.IsPerfectMatching := by
  let N := Padded.pairFamily G l r edges
  have hN := Padded.pairFamily_isMatching G l r edges dis
  have full : N.verts = {x | x ≠ v} := support
  have perfect := perfect_on_matched_verts G N hN
  rwa [full] at perfect

private theorem shift_to {n : ℕ} [NeZero n] (i j : Fin n) (distinct : i ≠ j) :
    ∃ π : Fin n ≃ Fin n, π i = j ∧ ∀ t, t ≠ π t := by
  let π := Equiv.addRight (j-i)
  refine ⟨π,add_sub_cancel i j,?_⟩
  intro t hit
  change t = t+(j-i) at hit
  have cancel : t+0 = t+(j-i) := (add_zero t).trans hit
  exact distinct (sub_eq_zero.mp (add_left_cancel cancel).symm).symm

/-- Replace a missing old label on the l side by the center. The single
opposite label assigned to it is known to be adjacent to the center. -/
private theorem old_label_repair (G : SimpleGraph X) [DecidableEq I] (o : X)
    (l r : I ↪ X) (dis : Disjoint (Set.range l) (Set.range r))
    (lo : ∀ i, l i ≠ o) (ro : ∀ i, r i ≠ o)
    (allLabels : ∀ x, x=o ∨ x ∈ Set.range l ∨ x ∈ Set.range r)
    (cross : ∀ i j, i ≠ j → G.Adj (l i) (r j)) (i : I) (π : I ≃ I)
    (derange : ∀ t, t ≠ π t) (special : G.Adj o (r (π i))) :
    ∃ M : (G.induce {x | x ≠ l i}).Subgraph, M.IsPerfectMatching := by
  classical
  let f (t : I) := if t = i then o else l t
  have inj : Function.Injective f := by
    intro a b eq
    by_cases ai : a=i <;> by_cases bi : b=i <;> simp [f,ai,bi] at eq <;>
      first | exact ai.trans bi.symm | exact (lo _ eq.symm).elim | exact (lo _ eq).elim | exact eq
  let left : I ↪ X := ⟨f,inj⟩
  let right := π.toEmbedding.trans r
  have ranged : Set.range right = Set.range r := by
    ext x
    constructor
    · rintro ⟨t,rfl⟩; exact ⟨π t,rfl⟩
    · rintro ⟨t,rfl⟩; exact ⟨π.symm t,congrArg r (π.apply_symm_apply t)⟩
  apply perfect_except_by_pairs G (l i) left right
  · intro t
    change G.Adj (if t=i then o else l t) (r (π t))
    split_ifs with same
    · exact same.symm ▸ special
    · exact cross t _ (derange t)
  · rw [ranged]
    apply Set.disjoint_left.mpr
    rintro _ ⟨t,rfl⟩ rightHit
    change (if t=i then o else l t) ∈ Set.range r at rightHit
    split_ifs at rightHit with same
    · obtain ⟨w,eq⟩ := rightHit; exact ro w eq
    · exact Set.disjoint_left.mp dis (Set.mem_range_self t) rightHit
  · rw [ranged]
    ext x
    constructor
    · intro inSet same
      subst x
      rcases inSet with ⟨t,ht⟩ | hit
      · change (if t=i then o else l t) = l i at ht
        split_ifs at ht with eq
        · exact lo i ht.symm
        · exact eq (l.injective ht)
      · exact Set.disjoint_left.mp dis (Set.mem_range_self i) hit
    · intro avoid
      rcases allLabels x with rfl | ⟨t,rfl⟩ | hit
      · exact Or.inl ⟨i,by simp [left,f]⟩
      · have neq : t ≠ i := fun h => avoid (congrArg l h)
        exact Or.inl ⟨t,by simp [left,f,neq]⟩
      · exact Or.inr hit

theorem zhao_factor_critical (d : ℕ) (hd : 2 ≤ d) : PerfectAfterEveryDeletion (zhaoGraph d) := by
  classical
  let _ : NeZero (2*d) := ⟨by omega⟩
  let l : Fin (2*d) ↪ ZhaoVertex d := ⟨zhaoLeft,fun _ _ h => Sum.inl.inj (Option.some.inj h)⟩
  let r : Fin (2*d) ↪ ZhaoVertex d := ⟨zhaoRight,fun _ _ h => Sum.inr.inj (Option.some.inj h)⟩
  have dis : Disjoint (Set.range l) (Set.range r) := Set.disjoint_left.mpr (by
    rintro _ ⟨a,rfl⟩ ⟨b,h⟩; cases h)
  have lo (t) : l t ≠ none := by intro h; cases h
  have ro (t) : r t ≠ none := by intro h; cases h
  have labels (x : ZhaoVertex d) : x=none ∨ x∈Set.range l ∨ x∈Set.range r := by
    rcases x with _ | ⟨i|i⟩
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨i,rfl⟩)
    · exact Or.inr (Or.inr ⟨i,rfl⟩)
  have cross (i j) (h : i≠j) : (zhaoGraph d).Adj (l i) (r j) := Or.inl h
  have pick_low (i : Fin (2*d)) : ∃ j : Fin (2*d), j.val<d ∧ i≠j := by
    by_cases hi : i.val=0
    · exact ⟨⟨1,by omega⟩,by change 1 < d; omega,fun eq => by have := congrArg Fin.val eq; simp_all⟩
    · exact ⟨⟨0,by omega⟩,by change 0 < d; omega,fun eq => hi (congrArg Fin.val eq)⟩
  intro v
  rcases v with _ | ⟨i|i⟩
  · let i : Fin (2*d) := ⟨0,by omega⟩
    obtain ⟨j,_,ij⟩ := pick_low i
    obtain ⟨π,_,derange⟩ := shift_to i j ij
    let right := π.toEmbedding.trans r
    apply perfect_except_by_pairs (zhaoGraph d) none l right (fun t => cross t (π t) (derange t))
    · apply Set.disjoint_left.mpr
      rintro _ ⟨t,rfl⟩ ⟨w,h⟩
      exact Set.disjoint_left.mp dis (Set.mem_range_self t) ⟨π w,h⟩
    · ext x
      constructor
      · rintro (⟨t,rfl⟩|⟨w,rfl⟩)
        · exact lo t
        · exact ro (π w)
      · intro ne
        rcases labels x with eq|h|⟨t,rfl⟩
        · exact (ne eq).elim
        · exact Or.inl h
        · exact Or.inr ⟨π.symm t,congrArg r (π.apply_symm_apply t)⟩
  · obtain ⟨j,low,ij⟩ := pick_low i
    obtain ⟨π,hit,derange⟩ := shift_to i j ij
    apply old_label_repair _ none l r dis lo ro labels cross i π derange
    change (π i).val < d
    rwa [hit]
  · obtain ⟨j,low,ij⟩ := pick_low i
    obtain ⟨π,hit,derange⟩ := shift_to i j ij
    apply old_label_repair _ none r l dis.symm ro lo (fun x => (labels x).imp_right Or.symm)
      (fun s t ne => (cross t s ne.symm).symm) i π derange
    change (π i).val < d
    rwa [hit]

#print axioms zhao_factor_critical
end JSP452Audit.StarHost
