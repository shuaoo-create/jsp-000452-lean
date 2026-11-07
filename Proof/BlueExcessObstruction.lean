import CappedColor
import ForcingHost
import HighStarCover

namespace JSP452Audit.StarHost
open SimpleGraph

variable {X : Type*} [Fintype X]

/-- Recolor exactly the original edges touching A red. -/
private def coverRecolor (G F : SimpleGraph X) (A : Set X) : SimpleGraph X :=
  F ⊔ (G ⊓ fromRel (fun x y => x ∈ A ∨ y ∈ A))

/-- Starting with a capped red graph and a strict blue excess budget, return
one coloring and two small controlling sets on the same original vertex type. -/
theorem cover_excess_coloring (G F : SimpleGraph X) (sub : F ≤ G) {q u v : ℕ}
    (hu : 0 < u) (hv : 0 < v)
    (strict : (∑ x, (Nat.card ((G \ F).neighborSet x) - q)) < u+v-1) :
    ∃ (R : SimpleGraph X) (A B : Set X), R ≤ G ∧ A.ncard ≤ u-1 ∧ B.ncard ≤ v-1 ∧
      (∀ ⦃x y⦄, R.Adj x y → x ∈ A ∨ y ∈ A ∨ F.Adj x y) ∧
      (∀ x, q < Nat.card ((G \ R).neighborSet x) → x ∈ B) := by
  classical
  let d (x : X) := Nat.card ((G \ F).neighborSet x)
  let bad := Finset.univ.filter (fun x => q < d x)
  have count : bad.card ≤ ∑ x, (d x - q) := by
    have bound := Finset.sum_le_sum (s := Finset.univ)
      (f := fun x => if q < d x then 1 else 0) (g := fun x => d x-q)
      (fun x _ => by split <;> omega)
    simpa [Finset.sum_boole, bad] using bound
  obtain ⟨A,sa,ca⟩ := Finset.exists_subset_card_eq (show min (u-1) bad.card ≤ bad.card from min_le_right _ _)
  let B := bad \ A
  let R := coverRecolor G F A
  have remain : B.card = bad.card-A.card := Finset.card_sdiff_of_subset sa
  have sumBound : (∑ x, (d x-q)) < u+v-1 := strict
  refine ⟨R,(A : Set X),(B : Set X),sup_le sub inf_le_left,?_,?_,?_,?_⟩
  · rw [Set.ncard_coe_finset,ca]
    exact min_le_left _ _
  · rw [Set.ncard_coe_finset,remain,ca]
    omega
  · intro x y edge
    rcases edge with old | added
    · exact Or.inr (Or.inr old)
    · rcases added.2.2 with hx | hy
      · exact hx.elim Or.inl (fun m => Or.inr (Or.inl m))
      · exact hy.elim (fun m => Or.inr (Or.inl m)) Or.inl
  · intro x high
    have incl : (G \ R).neighborSet x ⊆ (G \ F).neighborSet x :=
      fun _ e => ⟨e.1,fun f => e.2 (Or.inl f)⟩
    have monotone : Nat.card ((G \ R).neighborSet x) ≤ d x := Set.ncard_le_ncard incl
    have oldBad : x ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _,high.trans_le monotone⟩
    apply Finset.mem_sdiff.mpr
    refine ⟨oldBad,?_⟩
    intro member
    have empty : (G \ R).neighborSet x = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro y edge
      exact edge.2 (Or.inr ⟨edge.1,edge.1.ne,Or.inl (Or.inl member)⟩)
    rw [Nat.card_coe_set_eq,empty,Set.ncard_empty] at high
    omega

#print axioms cover_excess_coloring
/-- Strictly fewer than u+v−1 excess units suffice to exclude both complete
forests, whenever they require the indicated numbers of large stars. -/
theorem avoids_large_forests_of_blue_excess {I J : Type*} [Fintype I] [Fintype J]
    (G F : SimpleGraph X) (sub : F ≤ G) {p q u v : ℕ}
    (hu : 0 < u) (hv : 0 < v) (n : I → ℕ) (m : J → ℕ)
    (bigRed : u ≤ (Finset.univ.filter (fun i => p+1 ≤ n i)).card)
    (bigBlue : v ≤ (Finset.univ.filter (fun j => q+1 ≤ m j)).card)
    (cap : ∀ x, Nat.card (F.neighborSet x) ≤ p)
    (strict : (∑ x, (Nat.card ((G \ F).neighborSet x) - q)) < u+v-1) :
    ∃ R ≤ G, ¬ (forest n).IsContained R ∧ ¬ (forest m).IsContained (G \ R) := by
  obtain ⟨R,A,B,leG,smallA,smallB,edges,centers⟩ :=
    cover_excess_coloring G F sub hu hv strict
  refine ⟨R,leG,?_,?_⟩
  · intro red
    have bound := count_large_of_edge_cover R F A p n edges cap red
    omega
  · intro blue
    have bound := count_large_of_center_cover (G \ R) B q m centers blue
    omega

end JSP452Audit.StarHost

namespace JSP452Audit.Padded
open SimpleGraph JSP452Audit.StarHost

/-- A forcing host pays at least the combined large-star count less one in
its exact original-graph deficiency. The two original lists may have any sizes. -/
theorem Spec.forcing_minColorGap_of_large_stars {X I J : Type*}
    [Fintype X] [Fintype I] [Fintype J] (P : Spec X) [DecidableRel P.G.Adj]
    (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x) {p q u v : ℕ}
    (capA : ∀ x, P.A x = p) (capB : ∀ x, P.B x = q)
    (hu : 0 < u) (hv : 0 < v) (n : I → ℕ) (m : J → ℕ)
    (bigRed : u ≤ (Finset.univ.filter (fun i => p+1 ≤ n i)).card)
    (bigBlue : v ≤ (Finset.univ.filter (fun j => q+1 ≤ m j)).card)
    (forces : Forces P.G (forest n) (forest m)) : u+v-1 ≤ P.minColorGap := by
  by_contra! strict
  obtain ⟨F,sub,cap,loss⟩ := P.capped_optimal caps
  simp only [capA] at cap
  simp only [capB] at loss
  obtain ⟨R,incl,noRed,noBlue⟩ :=
    avoids_large_forests_of_blue_excess P.G F sub hu hv n m bigRed bigBlue cap (loss.trans_lt strict)
  exact (forces R incl).elim noRed noBlue

/-- Return actual original disjoint vertex sets certifying the obstruction. -/
theorem Spec.exists_original_cut_of_forcing_large_stars {X I J : Type*}
    [Fintype X] [Fintype I] [Fintype J] (P : Spec X) [DecidableRel P.G.Adj]
    (caps : ∀ x, P.G.degree x ≤ P.A x + P.B x) {p q u v : ℕ}
    (capA : ∀ x, P.A x = p) (capB : ∀ x, P.B x = q)
    (hu : 0 < u) (hv : 0 < v) (n : I → ℕ) (m : J → ℕ)
    (bigRed : u ≤ (Finset.univ.filter (fun i => p+1 ≤ n i)).card)
    (bigBlue : v ≤ (Finset.univ.filter (fun j => q+1 ≤ m j)).card)
    (forces : Forces P.G (forest n) (forest m)) :
    ∃ S T : Set X, Disjoint S T ∧ ((u+v-1 : ℕ) : ℤ) ≤ P.cutDeficit S T := by
  obtain ⟨S,T,dis,attains⟩ := (P.exact_factor_deficiency caps).2
  refine ⟨S,T,dis,?_⟩
  rw [attains]
  exact_mod_cast P.forcing_minColorGap_of_large_stars caps capA capB hu hv n m bigRed bigBlue forces

#print axioms Spec.exists_original_cut_of_forcing_large_stars

#print axioms Spec.forcing_minColorGap_of_large_stars
end JSP452Audit.Padded
