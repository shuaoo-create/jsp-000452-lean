import AsymAllocation
import AsymBlock
import PositiveCutPacking
import NoUnitsKernel
import ShiftViaFunding

namespace JSP452Audit.StarHost
open SimpleGraph

/-- Concrete local coloring and cut-set shares, chosen on the actual
    components of the original induced graph outside the barrier. -/
theorem mixed_local_choices_of_cut {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (p q : ℕ) (budget : S.ncard + halfComponents (G.induce Sᶜ) ≤ p+q)
    (balance : S.ncard + halfComponents (G.induce Sᶜ) ≤ 2*q+1)
    [Fintype (G.induce Sᶜ).ConnectedComponent] :
    ∃ A ⊆ S, ∃ red blue : (G.induce Sᶜ).ConnectedComponent → ℕ,
      A.ncard + (∑ c, red c) ≤ p ∧
      (S \ A).ncard + (∑ c, blue c) ≤ q ∧
      ∀ c : (G.induce Sᶜ).ConnectedComponent, ∃ R ≤ (G.induce Sᶜ).induce c.supp,
        PosCapacity R (red c) ∧ BlockCapacity ((G.induce Sᶜ).induce c.supp \ R) (blue c) := by
  classical
  let cost (c : (G.induce Sᶜ).ConnectedComponent) := c.supp.ncard / 2
  have b : S.ncard + (∑ c, cost c) ≤ p+q := by
    unfold halfComponents at budget
    have h := Subsingleton.elim (Fintype.ofFinite (G.induce Sᶜ).ConnectedComponent) (inferInstance : Fintype (G.induce Sᶜ).ConnectedComponent)
    rw [h] at budget
    exact budget
  have bal : S.ncard + (∑ c, cost c) ≤ 2*q+1 := by
    unfold halfComponents at balance
    have h := Subsingleton.elim (Fintype.ofFinite (G.induce Sᶜ).ConnectedComponent) (inferInstance : Fintype (G.induce Sᶜ).ConnectedComponent)
    rw [h] at balance
    exact balance
  obtain ⟨br,bb,red,blue,parts,blockEq,okR,okB,share⟩ := asymmetric_barrier_allocation cost S.ncard p q b bal
  obtain ⟨A,subA,cardA⟩ := Set.exists_subset_card_eq (s := S) (n := br) (by omega)
  have blueA := Set.ncard_sdiff_add_ncard_of_subset subA
  refine ⟨A,subA,red,blue,by omega,by omega,?_⟩
  intro c
  apply asym_block_color
  · rw [blockEq c,Nat.card_coe_set_eq]
    unfold cost
    omega
  · exact share c


/-- Low matching number yields one actual red subgraph simultaneously avoiding
    any red high-leaf forest of p+1 components and blue such forest of q+1. -/
theorem mixed_color_from_matching_budget {X : Type*} [Finite X]
    (G : SimpleGraph X) (p q : ℕ) (low : matchingEdges G ≤ p+q) (balance : matchingEdges G ≤ 2*q+1) :
    ∃ R ≤ G, PosCapacity R p ∧ BlockCapacity (G \ R) q := by
  classical
  obtain ⟨S,budget⟩ := barrier_at_matching_number G
  let Y := G.induce Sᶜ
  let _ := Fintype.ofFinite Y.ConnectedComponent
  obtain ⟨A,inCut,pr,pb,totR,totB,canColor⟩ :=
    mixed_local_choices_of_cut G S p q (budget.trans low) (budget.trans balance)
  choose r sub redOK blueOK using canColor
  let R := barrierRed G S A r
  have rle : R ≤ G := barrierRed_le G S A r
  have rc (c : Y.ConnectedComponent) :
      PosCapacity (R.comap (fun z : c.supp => z.val.val)) (pr c) := by
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
  have red := positive_cut_packing_capacity G R S A pr rle
    (fun {_ _} h hx => ((barrierRed_at_cut G S A r (Or.inl hx)).mp h).2) rc
  have blue := cut_packing_capacity G (G \ R) S (S \ A) pb sdiff_le
    (fun {_ _} h hx => barrierBlue_uses_control G S A r (Or.inl hx) h) bc
  exact ⟨R,rle,fun k n hn copy => (red k n hn copy).trans totR,
    fun k m hm copy => (blue k m hm copy).trans totB⟩


theorem mixed_matching_floor {X : Type*} [Finite X] {s t : ℕ}
    (G : SimpleGraph X) (hs : 0<s) (ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ)
    (red : ∀ i, 1≤n i) (blue : ∀ j, 2≤m j) (length : s≤t+1)
    (force : Forces G (forest n) (forest m)) : s+t-1 ≤ matchingEdges G := by
  by_contra! low
  obtain ⟨R,rle,noRed,noBlue⟩ := mixed_color_from_matching_budget G (s-1) (t-1) (by omega) (by omega)
  rcases force R rle with hr | hb
  · have := noRed s n red hr
    omega
  · have := noBlue t m blue hb
    omega

theorem mixed_one_two_exact {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (red : ∀ i, 1≤n i) (upper : ∀ i, n i≤2) (blue : ∀ j, 2≤m j) (length : s≤t+1) :
    sizeRamsey (forest n) (forest m) = ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k := by
  apply exact_of_forcing_lower
  intro N G force
  have rank := mixed_matching_floor G hs ht n m red blue length force
  have costs := small_host_budget hs ht n m hn hm red (fun j => by have := blue j; omega) (Or.inl upper) G force
  omega

#print axioms mixed_matching_floor
#print axioms mixed_one_two_exact
end JSP452Audit.StarHost
