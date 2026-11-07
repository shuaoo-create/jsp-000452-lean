import OriginalFailureEscapeClassification
import Mathlib.Combinatorics.SimpleGraph.VertexCover
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
variable {X : Type*} [Finite X]

omit [Finite X] in
theorem cover_residual_empty (G : SimpleGraph X) (C : Set X) (cover : G.IsVertexCover C) :
    G.induce Cᶜ = ⊥ := by
  rw [eq_bot_iff_forall_not_adj]
  intro x y e
  exact (cover e).elim x.property y.property

/-- A vertex cover must meet at least as many labels as there are
remaining original row columns, even when the cover includes isolated labels. -/
theorem forcing_row_cover_length {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (G : SimpleGraph X)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (C : Set X) (cover : G.IsVertexCover C) : rowCount s t r ≤ C.ncard := by
  by_contra! small
  have live : r+C.ncard<s+t-1 := by dsimp [rowCount] at small;omega
  have next := row_delete_set G C _ _ (pad_antitone n hn) (pad_antitone m hm)
    (pad_positive n pn) (pad_positive m pm) row
  obtain ⟨i,j,sum,_⟩ := diagonal_attained n m hs ht _ live
  obtain ⟨v,fee⟩ := select_blue_center _ n m pn next i j sum
  rw [cover_residual_empty G C cover] at fee
  have zero : Nat.card ((⊥:SimpleGraph ↥Cᶜ).neighborSet v)=0 := by simp
  have pos := pm j
  omega

omit [Finite X] in
/-- Restricting a cover to a region keeps precisely its original labels. -/
theorem cover_induced_ncard (G : SimpleGraph X) (U C : Set X) (cover : G.IsVertexCover C) :
    (G.induce U).IsVertexCover {v : U | v.val∈C} ∧
      ({v : U | v.val∈C} : Set U).ncard = (U∩C).ncard := by
  constructor
  · intro x y e;exact cover e
  · apply Nat.card_congr
    exact { toFun := fun v => ⟨v.val.val,v.val.property,v.property⟩
            invFun := fun v => ⟨⟨v.val,v.property.1⟩,v.property.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }

/-- An escaping original list gives a cover floor k+d on the actual exterior.
The same assertion holds regardless of which color escaped. -/
theorem strict_escape_exterior_cover (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1))
    (C : Set F.X) (cover : F.G.IsVertexCover C) :
    matchingEdges (F.G.induce K.rest)+(F.rank-matchingEdges F.G) ≤ (K.rest∩C).ncard := by
  let μ := matchingEdges (F.G.induce K.core)
  obtain ⟨restricted,count⟩ := cover_induced_ncard F.G K.rest C cover
  have escape := strict_source_one_list_escapes F paid K
  have prices := strict_exterior_whole_tail_prices F paid K
  rw [←count]
  by_cases red : μ<F.s
  · rw [←(prices.1 red).1]
    exact forcing_row_cover_length (by omega : 0<F.s-μ) F.ht _ _ (remainingDemand_antitone F.n F.hn μ)
      F.hm (remainingDemand_positive F.n F.pn μ) F.pm _ (exterior_complete_red_tail F.G K F.n F.m F.hn F.hm F.pn F.pm F.row) _ restricted
  · have blue : μ<F.t := by change μ+(F.rank-matchingEdges F.G)<max F.s F.t at escape;omega
    rw [←(prices.2 blue).1]
    exact forcing_row_cover_length F.hs (by omega : 0<F.t-μ) _ _ F.hn (remainingDemand_antitone F.m F.hm μ)
      F.pn (remainingDemand_positive F.m F.pm μ) _ (exterior_complete_blue_tail F.G K F.n F.m F.hn F.hm F.pn F.pm F.row) _ restricted

#print axioms forcing_row_cover_length
#print axioms cover_induced_ncard
#print axioms strict_escape_exterior_cover
end JSP452Audit.StarHost
