import BarrierGlueColor
import CutLocalChoices
import GraphMatchBarrier
import CutPacking
import SmallSideInterval

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Low matching number yields one actual red subgraph simultaneously avoiding
    any red high-leaf forest of p+1 components and blue such forest of q+1. -/
theorem color_from_matching_budget {X : Type*} [Finite X]
    (G : SimpleGraph X) (p q : ℕ) (low : matchingEdges G ≤ p+q) :
    ∃ R ≤ G, BlockCapacity R p ∧ BlockCapacity (G \ R) q := by
  classical
  obtain ⟨S,budget⟩ := barrier_at_matching_number G
  let Y := G.induce Sᶜ
  let _ := Fintype.ofFinite Y.ConnectedComponent
  obtain ⟨A,inCut,pr,pb,totR,totB,canColor⟩ :=
    local_choices_of_cut G S p q (budget.trans low)
  choose r sub redOK blueOK using canColor
  let R := barrierRed G S A r
  have rle : R ≤ G := barrierRed_le G S A r
  have rc (c : Y.ConnectedComponent) :
      BlockCapacity (R.comap (fun z : c.supp => z.val.val)) (pr c) := by
    have eq : R.comap (fun z : c.supp => z.val.val) = r c := by
      ext x y
      exact barrierRed_in_block G S A inCut r sub c x y
    rw [eq]
    exact redOK c
  have bc (c : Y.ConnectedComponent) :
      BlockCapacity ((G \ R).comap (fun z : c.supp => z.val.val)) (pb c) := by
    have eq : (G \ R).comap (fun z : c.supp => z.val.val) = Y.induce c.supp \ r c := by
      ext x y
      exact barrierBlue_in_block G S A inCut r sub c x y
    rw [eq]
    exact blueOK c
  have red := cut_packing_capacity G R S A pr rle
    (fun {_ _} h hx => ((barrierRed_at_cut G S A r (Or.inl hx)).mp h).2) rc
  have blue := cut_packing_capacity G (G \ R) S (S \ A) pb sdiff_le
    (fun {_ _} h hx => barrierBlue_uses_control G S A r (Or.inl hx) h) bc
  exact ⟨R,rle,fun k n hn copy => (red k n hn copy).trans totR,
    fun k m hm copy => (blue k m hm copy).trans totB⟩

theorem unit_free_matching_floor {X : Type*} [Finite X] {s t : ℕ}
    (G : SimpleGraph X) (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (red : ∀ i, 2≤n i) (blue : ∀ j, 2≤m j) (force : Forces G (forest n) (forest m)) :
    s+t-1 ≤ matchingEdges G := by
  by_contra! low
  obtain ⟨R,rle,noRed,noBlue⟩ := color_from_matching_budget G (s-1) (t-1) (by omega)
  rcases force R rle with hr | hb
  · have := noRed s n red hr
    omega
  · have := noBlue t m blue hb
    omega

/-- Complete original equality for a forest of two-leaf stars versus *any*
    star forest without isolated-edge components, in either orientation. -/
theorem two_leaf_vs_unit_free_exact {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (red : ∀ i, 2≤n i) (blue : ∀ j, 2≤m j)
    (two : (∀ i, n i=2) ∨ (∀ j, m j=2)) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  apply le_antisymm (erdos561_upper n m)
  obtain ⟨N,G,edge,force⟩ := star_min_attained n m
  have wide := unit_free_matching_floor G hs ht n m red blue force
  have bound := small_host_budget hs ht n m hn hm (fun i => by have := red i; omega)
    (fun j => by have := blue j; omega) (two.imp (fun h i => (h i).le) (fun h j => (h j).le)) G force
  omega

#print axioms color_from_matching_budget
#print axioms unit_free_matching_floor
#print axioms two_leaf_vs_unit_free_exact
end JSP452Audit.StarHost
