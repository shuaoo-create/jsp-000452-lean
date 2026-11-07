import TutteCutLanguage
import Mathlib.Data.Fintype.Sum

namespace JSP452Audit.StarHost
open SimpleGraph

/-- A vertex adjacent to all others belongs to every Tutte obstruction
    in a finite graph of even order. -/
theorem universal_in_violator {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (bad : G.IsTutteViolator S) (even : Even (Nat.card X))
    (u : X) (univ : ∀ x, x ≠ u → G.Adj x u) : u ∈ S := by
  classical
  by_contra absent
  let z : ↥(Sᶜ : Set X) := ⟨u,absent⟩
  let H := G.induce Sᶜ
  have all : ∀ y, y ≠ z → H.Adj y z := fun y neq => univ y.val (fun eq => neq (Subtype.ext eq))
  have one := odd_le_one_of_universal H z all
  have tooMany : S.ncard < H.oddComponents.ncard := (tutte_violator_induce G S).mp bad
  have zero : S.ncard=0 := by omega
  have oddC : Odd H.oddComponents.ncard := by rw [show H.oddComponents.ncard=1 by omega]; decide
  have oddV := H.odd_ncard_oddComponents.mp oddC
  have size : Nat.card ↥(Sᶜ : Set X) = Nat.card X := by
    rw [Nat.card_coe_set_eq, Set.ncard_compl,zero,Nat.sub_zero]
  rw [size] at oddV
  exact (Nat.not_odd_iff_even.mpr even) oddV

private def cutParts {X : Type*} {d : ℕ} (U : Set (X ⊕ Fin d))
    (all : ∀ i, Sum.inr i ∈ U) :
    U ≃ ({x : X // Sum.inl x ∈ U} ⊕ Fin d) where
  toFun
    | ⟨.inl x,h⟩ => .inl ⟨x,h⟩
    | ⟨.inr i,_⟩ => .inr i
  invFun
    | .inl x => ⟨.inl x.val,x.property⟩
    | .inr i => ⟨.inr i,all i⟩
  left_inv := by rintro ⟨x | i,h⟩ <;> rfl
  right_inv := by rintro (⟨x,h⟩ | i) <;> rfl

/-- Once all added vertices are deleted, the residual graph is the original
    graph with precisely the old members of that same cut removed. -/
private def outsideJoinIso {X : Type*} {d : ℕ} (G : SimpleGraph X) (H : SimpleGraph (X ⊕ Fin d))
    (old : ∀ x y, H.Adj (.inl x) (.inl y) ↔ G.Adj x y) (U : Set (X ⊕ Fin d))
    (all : ∀ i, Sum.inr i ∈ U) :
    G.induce {x | (Sum.inl x : X ⊕ Fin d) ∉ U} ≃g H.induce Uᶜ where
  toFun x := ⟨.inl x.val,x.property⟩
  invFun
    | ⟨.inl x,h⟩ => ⟨x,h⟩
    | ⟨.inr i,h⟩ => False.elim (h (all i))
  left_inv _ := rfl
  right_inv := by
    rintro ⟨x | i,h⟩
    · rfl
    · exact False.elim (h (all i))
  map_rel_iff' := by intro x y; exact old _ _

theorem old_odd_cut_of_join_violator {X : Type*} [Finite X] {d : ℕ}
    (G : SimpleGraph X) (H : SimpleGraph (X ⊕ Fin d))
    (old : ∀ x y, H.Adj (.inl x) (.inl y) ↔ G.Adj x y)
    (univ : ∀ (i : Fin d) (x : X ⊕ Fin d), x ≠ .inr i → H.Adj x (.inr i))
    (even : Even (Nat.card X+d)) (U : Set (X ⊕ Fin d)) (bad : H.IsTutteViolator U) :
    ∃ S : Set X, S.ncard+d < (G.induce Sᶜ).oddComponents.ncard := by
  classical
  let _ := Fintype.ofFinite X
  have evenH : Even (Nat.card (X ⊕ Fin d)) := by simpa only [Nat.card_sum,Nat.card_fin] using even
  have all : ∀ i, Sum.inr i ∈ U := fun i => universal_in_violator H U bad evenH _ (univ i)
  let S : Set X := {x | (Sum.inl x : X ⊕ Fin d) ∈ U}
  refine ⟨S,?_⟩
  have eq := Nat.card_congr (cutParts U all)
  rw [Nat.card_sum,Nat.card_fin] at eq
  have cu : U.ncard = S.ncard + d := eq
  have comps := odd_ncard_iso (outsideJoinIso G H old U all)
  have ht := (tutte_violator_induce H U).mp bad
  rw [cu,← comps] at ht
  exact ht

#print axioms old_odd_cut_of_join_violator
end JSP452Audit.StarHost
