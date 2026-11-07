import RankSplitDef
import CutVertexSupportBound

namespace JSP452Audit.StarHost
open SimpleGraph

private theorem twice_rank_le_support {X : Type*} [Finite X] (C : SimpleGraph X) (U : Set X)
    (support : ∀ ⦃x y⦄, C.Adj x y → x∈U) : 2*matchingEdges C ≤ U.ncard := by
  obtain ⟨M,hm,size⟩ := exists_maximum_matching C
  have sub : M.verts ⊆ U := by
    intro x used
    obtain ⟨y,h,_⟩ := hm used
    exact support (M.adj_sub h)
  have card := Set.ncard_le_ncard sub
  rwa [matching_vertices_eq_twice_edges hm,size] at card

private def initialVertices (n a : ℕ) : Set (Fin n) := {v | v.val < a}

private theorem prefix_card {n a : ℕ} (fit : a ≤ n) : (initialVertices n a).ncard = a := by
  let e : initialVertices n a ≃ Fin a :=
    { toFun := fun x => ⟨x.val.val,x.property⟩
      invFun := fun i => ⟨⟨i.val,i.isLt.trans_le fit⟩,i.isLt⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (Nat.card_fin _)

/-- A crossing cycle edge can touch the initialVertices only at zero or its last
index. This modular argument also works for n=0,1,2. -/
private theorem prefix_boundary_le_two {n a : ℕ} (G : SimpleGraph (Fin n))
    (cyclic : G ≤ cycleGraph n) : (insideCutBoundary G (initialVertices n a)).ncard ≤ 2 := by
  let B := insideCutBoundary G (initialVertices n a)
  have sides (x : B) : x.val.val = 0 ∨ x.val.val+1 = a := by
    obtain ⟨hx,y,hy,xy⟩ := x.property
    change x.val.val < a at hx
    change ¬ y.val < a at hy
    have lt : x.val.val < y.val := by omega
    have yl := y.isLt
    rcases cycleGraph_adj'.mp (cyclic xy) with h | h
    · rw [Fin.val_sub,Nat.mod_eq_of_lt (by omega)] at h
      exact Or.inl (by omega)
    · rw [Fin.sub_val_of_le (show x.val ≤ y from lt.le)] at h
      exact Or.inr (by omega)
  let side (x : B) : Fin 2 := if x.val.val = 0 then 0 else 1
  have inj : Function.Injective side := by
    intro x y same
    have sx := sides x
    have sy := sides y
    apply Subtype.ext
    apply Fin.ext
    by_cases hx : x.val.val = 0 <;> by_cases hy : y.val.val = 0 <;>
      simp [side,hx,hy] at same <;> omega
  change B.ncard ≤ 2
  rw [← Nat.card_coe_set_eq]
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective side inj

/-- All graphs between the indexed spanning path and the indexed cycle share
the rank and the boundary estimate for the same initial segment of 2u vertices. -/
theorem canSplitRank_between_path_cycle (n : ℕ) (G : SimpleGraph (Fin n))
    (path : pathGraph n ≤ G) (cyclic : G ≤ cycleGraph n) : CanSplitRank G := by
  intro u budget
  have rank := matchingEdges_of_spanning_path n G path
  let U := initialVertices n (2*u)
  have len : U.ncard = 2*u := prefix_card (by omega)
  have boundary : (insideCutBoundary G U).ncard ≤ 2 := prefix_boundary_le_two G cyclic
  let R := internalRed G U
  have redBound := twice_rank_le_support R U (by intro x y h; exact h.2.1)
  have blueSup : ∀ ⦃x y⦄, (G \ R).Adj x y → x ∈ Uᶜ ∪ insideCutBoundary G U := by
    intro x y h
    by_cases hx : x ∈ U
    · exact Or.inr ⟨hx,y,fun hy => h.2 ⟨h.1,hx,hy⟩,h.1⟩
    · exact Or.inl hx
  have blueBound := (twice_rank_le_support _ _ blueSup).trans (Set.ncard_union_le _ _)
  have all := Set.ncard_add_ncard_compl U
  rw [Nat.card_fin] at all
  exact ⟨R,fun _ _ h => h.1,by omega,by omega⟩

theorem canSplitRank_pathGraph (n : ℕ) : CanSplitRank (pathGraph n) :=
  canSplitRank_between_path_cycle n _ le_rfl pathGraph_le_cycleGraph

theorem canSplitRank_cycleGraph (n : ℕ) : CanSplitRank (cycleGraph n) :=
  canSplitRank_between_path_cycle n _ pathGraph_le_cycleGraph le_rfl

#print axioms canSplitRank_pathGraph
#print axioms canSplitRank_cycleGraph
end JSP452Audit.StarHost
