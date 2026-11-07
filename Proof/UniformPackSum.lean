import UniformSubforest
import Mathlib.Combinatorics.SimpleGraph.Sum

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem uniform_lands_in_part {Z X : Type*} {H : SimpleGraph Z} {C : SimpleGraph X}
    {a k l : ℕ} (f : (forest (fun _ : Fin k => a)).Copy H) (part : C ↪g H)
    (labels : Fin l ↪ Fin k)
    (lands : ∀ i : Fin l, ∀ j : Fin (a+1), ∃ x : X, part x = f ⟨labels i,j⟩) :
    (forest (fun _ : Fin l => a)).IsContained C := by
  let target := fun _ : Fin l => a
  let sub := subforestCopy target (fun _ : Fin k => a) labels (fun _ => le_rfl)
  let g (u : Vertices target) := (lands u.1 u.2).choose
  have image (u : Vertices target) : part (g u) = f (sub u) := (lands u.1 u.2).choose_spec
  refine ⟨{toHom := {toFun := g, map_rel' := ?_}, injective' := ?_}⟩
  · intro u v edge
    apply part.map_rel_iff.mp
    rw [image,image]; exact f.toHom.map_adj (sub.toHom.map_adj edge)
  · intro u v same
    exact sub.injective (f.injective ((image u).symm.trans ((congrArg part same).trans (image v))))

/-- Split a single uniform forest copy according to the summand of each center.
The split includes every leaf and all the original component labels exactly once. -/
theorem uniform_copy_split_sum {X Y : Type*} (C : SimpleGraph X) (E : SimpleGraph Y) (a k : ℕ)
    (copy : (forest (fun _ : Fin k => a)).IsContained (C ⊕g E)) :
    ∃ l r : ℕ, l+r=k ∧ (forest (fun _ : Fin l => a)).IsContained C ∧
      (forest (fun _ : Fin r => a)).IsContained E := by
  classical
  obtain ⟨f⟩ := copy
  let n := fun _ : Fin k => a
  have edgeSide {x y : X ⊕ Y} (edge : (C ⊕g E).Adj x y) : x.isLeft = y.isLeft := by
    rcases x with x|x <;> rcases y with y|y
    · rfl
    · exact (not_adj_sum_inl_inr _ _ edge).elim
    · exact (not_adj_sum_inl_inr _ _ edge.symm).elim
    · rfl
  have side (i : Fin k) (j : Fin (a+1)) :
      (f ⟨i,j⟩).isLeft = (f (center n i)).isLeft := by
    refine Fin.cases rfl (fun b => ?_) j
    exact (edgeSide (f.toHom.map_adj (starEdge n ⟨i,b⟩))).symm
  let P (i : Fin k) := (f (center n i)).isLeft = true
  let L := {i : Fin k // P i}
  let R := {i : Fin k // ¬P i}
  let el := (Fintype.equivFin L).symm
  let er := (Fintype.equivFin R).symm
  let left := el.toEmbedding.trans (Function.Embedding.subtype P)
  let right := er.toEmbedding.trans (Function.Embedding.subtype (fun i => ¬P i))
  have counts := Nat.card_congr (Equiv.sumCompl P)
  refine ⟨Fintype.card L,Fintype.card R,?_,?_,?_⟩
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_sum,Fintype.card_fin,L,R] using counts
  · apply uniform_lands_in_part f (Embedding.sumInl : C ↪g C ⊕g E) left
    intro i j
    have same := side (left i) j
    have ct : (f (center n (left i))).isLeft = true := (el i).property
    cases h : f ⟨left i,j⟩ with
    | inl x => exact ⟨x,rfl⟩
    | inr y => simp [h,ct] at same
  · apply uniform_lands_in_part f (Embedding.sumInr : E ↪g C ⊕g E) right
    intro i j
    have same := side (right i) j
    have ct : (f (center n (right i))).isLeft ≠ true := (er i).property
    cases h : f ⟨right i,j⟩ with
    | inl x => simp [h,ct] at same
    | inr y => exact ⟨y,rfl⟩

private theorem uniform_count_le_of_absent {X : Type*} (C : SimpleGraph X) (a p l : ℕ)
    (no : ¬(forest (fun _ : Fin (p+1) => a)).IsContained C)
    (yes : (forest (fun _ : Fin l => a)).IsContained C) : l ≤ p := by
  by_contra! large
  obtain ⟨f⟩ := yes
  exact no ⟨f.comp (subforestCopy _ _ (Fin.castLEEmb (show p+1 ≤ l from large)) (fun _ => le_rfl))⟩

theorem uniform_copy_count_le_sum {X Y : Type*} (C : SimpleGraph X) (E : SimpleGraph Y)
    (a p q : ℕ) (noLeft : ¬(forest (fun _ : Fin (p+1) => a)).IsContained C)
    (noRight : ¬(forest (fun _ : Fin (q+1) => a)).IsContained E)
    (k : ℕ) (copy : (forest (fun _ : Fin k => a)).IsContained (C ⊕g E)) : k ≤ p+q := by
  obtain ⟨l,r,total,lc,rc⟩ := uniform_copy_split_sum C E a k copy
  rw [← total]
  exact Nat.add_le_add (uniform_count_le_of_absent C a p l noLeft lc)
    (uniform_count_le_of_absent E a q r noRight rc)

theorem uniform_absent_in_sum {X Y : Type*} (C : SimpleGraph X) (E : SimpleGraph Y)
    (a p q : ℕ) (noLeft : ¬(forest (fun _ : Fin (p+1) => a)).IsContained C)
    (noRight : ¬(forest (fun _ : Fin (q+1) => a)).IsContained E) :
    ¬(forest (fun _ : Fin (p+q+1) => a)).IsContained (C ⊕g E) := by
  intro copy
  have := uniform_copy_count_le_sum C E a p q noLeft noRight _ copy
  omega

#print axioms uniform_copy_split_sum
#print axioms uniform_copy_count_le_sum
#print axioms uniform_absent_in_sum
end JSP452Audit.StarHost
