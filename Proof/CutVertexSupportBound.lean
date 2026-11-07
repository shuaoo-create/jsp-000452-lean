import ForcingHost
import AvoidIsolated
import RegionWeights

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*}

/-- Original vertices of U incident with a real edge to its exterior. -/
def insideCutBoundary (G : SimpleGraph X) (U : Set X) : Set X :=
  {x | x ∈ U ∧ ∃ y ∈ Uᶜ, G.Adj x y}

/-- Red consists of precisely the original edges internal to U. -/
def internalRed (G : SimpleGraph X) (U : Set X) : SimpleGraph X where
  Adj x y := G.Adj x y ∧ x ∈ U ∧ y ∈ U
  symm := ⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
  loopless := ⟨fun _ h => h.1.ne rfl⟩

theorem insideCutBoundary_le_cross [Finite X] (G : SimpleGraph X) (U : Set X) :
    (insideCutBoundary G U).ncard ≤ crossCount G U Uᶜ := by
  let E := {p : ↥U × ↥(Uᶜ : Set X) // G.Adj p.1.val p.2.val}
  let endpoint (e : E) : insideCutBoundary G U :=
    ⟨e.val.1.val,e.val.1.property,e.val.2.val,e.val.2.property,e.property⟩
  have onto : Function.Surjective endpoint := by
    rintro ⟨x,hx,y,hy,edge⟩
    exact ⟨⟨(⟨x,hx⟩,⟨y,hy⟩),edge⟩,rfl⟩
  exact Nat.card_le_card_of_surjective endpoint onto

private theorem order_le_support {A : Type*} [Finite X] (F : SimpleGraph A) (C : SimpleGraph X)
    (U : Set X) (positive : ∀ x, ∃ y, F.Adj x y)
    (support : ∀ ⦃x y⦄, C.Adj x y → x ∈ U) (copy : F.IsContained C) : Nat.card A ≤ U.ncard := by
  obtain ⟨f⟩ := copy
  have lands (x : A) : f x ∈ U := by
    obtain ⟨y,edge⟩ := positive x
    exact support (f.toHom.map_adj edge)
  let inc (x : A) : U := ⟨f x,lands x⟩
  exact Nat.card_le_card_of_injective inc (fun _ _ h => f.injective (congrArg Subtype.val h))

/-- Both support bounds hold for this single specified coloring, for arbitrary
targets without isolated vertices. A boundary vertex is charged only once. -/
theorem internal_cut_supports {A B : Type*} [Finite X]
    (G : SimpleGraph X) (U : Set X) (F : SimpleGraph A) (H : SimpleGraph B)
    (pF : ∀ x, ∃ y, F.Adj x y) (pH : ∀ x, ∃ y, H.Adj x y) :
    let R := internalRed G U
    R ≤ G ∧ (F.IsContained R → Nat.card A ≤ U.ncard) ∧
      (H.IsContained (G \ R) → Nat.card B ≤ Uᶜ.ncard + (insideCutBoundary G U).ncard) := by
  intro R
  refine ⟨fun _ _ h => h.1,order_le_support F R U pF (fun _ _ h => h.2.1),?_⟩
  intro blue
  have supported : ∀ ⦃x y⦄, (G \ R).Adj x y → x ∈ Uᶜ ∪ insideCutBoundary G U := by
    intro x y h
    by_cases hx : x ∈ U
    · exact Or.inr ⟨hx,y,(fun hy => h.2 ⟨h.1,hx,hy⟩),h.1⟩
    · exact Or.inl hx
  exact (order_le_support H _ _ pH supported blue).trans (Set.ncard_union_le _ _)

theorem cut_avoids_positive_forests {I J : Type*} [Finite X]
    (G : SimpleGraph X) (U : Set X) (n : I → ℕ) (m : J → ℕ)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j) (redSmall : U.ncard < Nat.card (Vertices n))
    (blueSmall : Uᶜ.ncard + (insideCutBoundary G U).ncard < Nat.card (Vertices m)) :
    ∃ R ≤ G, ¬ (forest n).IsContained R ∧ ¬ (forest m).IsContained (G \ R) := by
  obtain ⟨sub,red,blue⟩ := internal_cut_supports G U (forest n) (forest m)
    (forest_has_neighbor n pn) (forest_has_neighbor m pm)
  exact ⟨_,sub,fun f => (Nat.not_le_of_lt redSmall) (red f),fun h => (Nat.not_le_of_lt blueSmall) (blue h)⟩

/-- Cover accounting in Liu's direct argument: the crossing cover edges
are at most two, and extra counts the remaining edges. This identity-level
input keeps the argument independent of how the candidate cover was found. -/
theorem cover_order_bound_of_crossing {I J : Type*} [Finite X]
    (G : SimpleGraph X) (U : Set X) (n : I → ℕ) (m : J → ℕ)
    (pn : ∀ i, 1 ≤ n i) (pm : ∀ j, 1 ≤ m j)
    (force : Forces G (forest n) (forest m)) (extra paths : ℕ)
    (oneShort : U.ncard+1 = Nat.card (Vertices n))
    (cross : crossCount G U Uᶜ ≤ 2+extra)
    (edgeBudget : Nat.card X + extra ≤ G.edgeSet.ncard+paths) :
    Nat.card (Vertices n) + Nat.card (Vertices m) ≤ G.edgeSet.ncard+paths+3 := by
  obtain ⟨sub,red,blue⟩ := internal_cut_supports G U (forest n) (forest m)
    (forest_has_neighbor n pn) (forest_has_neighbor m pm)
  have boundary := insideCutBoundary_le_cross G U
  have vertices := Set.ncard_add_ncard_compl U
  rcases force (internalRed G U) sub with redCopy | blueCopy
  · have impossible := red redCopy
    omega
  · have blueBound := blue blueCopy
    omega

#print axioms insideCutBoundary_le_cross
#print axioms cut_avoids_positive_forests
#print axioms cover_order_bound_of_crossing
end JSP452Audit.StarHost
