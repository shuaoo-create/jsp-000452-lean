import BarrierAllocation
import BlockColor
import ComponentBudget
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Concrete local coloring and cut-set shares, chosen on the actual
    components of the original induced graph outside the barrier. -/
theorem local_choices_of_cut {X : Type*} [Finite X] (G : SimpleGraph X) (S : Set X)
    (p q : ℕ) (budget : S.ncard + halfComponents (G.induce Sᶜ) ≤ p+q)
    [Fintype (G.induce Sᶜ).ConnectedComponent] :
    ∃ A ⊆ S, ∃ red blue : (G.induce Sᶜ).ConnectedComponent → ℕ,
      A.ncard + (∑ c, red c) ≤ p ∧
      (S \ A).ncard + (∑ c, blue c) ≤ q ∧
      ∀ c : (G.induce Sᶜ).ConnectedComponent, ∃ R ≤ (G.induce Sᶜ).induce c.supp,
        BlockCapacity R (red c) ∧ BlockCapacity ((G.induce Sᶜ).induce c.supp \ R) (blue c) := by
  classical
  let cost (c : (G.induce Sᶜ).ConnectedComponent) := c.supp.ncard / 2
  have b : S.ncard + (∑ c, cost c) ≤ p+q := by
    unfold halfComponents at budget
    have h := Subsingleton.elim (Fintype.ofFinite (G.induce Sᶜ).ConnectedComponent) (inferInstance : Fintype (G.induce Sᶜ).ConnectedComponent)
    rw [h] at budget
    exact budget
  obtain ⟨br,bb,red,blue,parts,blockEq,okR,okB⟩ := barrier_allocation cost S.ncard p q b
  obtain ⟨A,subA,cardA⟩ := Set.exists_subset_card_eq (s := S) (n := br) (by omega)
  have blueA := Set.ncard_sdiff_add_ncard_of_subset subA
  refine ⟨A,subA,red,blue,by omega,by omega,?_⟩
  intro c
  apply block_color_capacity
  rw [blockEq c,Nat.card_coe_set_eq]
  unfold cost
  omega

#print axioms local_choices_of_cut
end JSP452Audit.StarHost
