import GoodPortClassification
import SmallComplementFacts
import DegreeRegion
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

theorem odd_good_component_is_small_clique [Nonempty X] (Q : SimpleGraph X) (D : ℕ)
    (odd : Odd D) (cap : ∀x,Nat.card (Q.neighborSet x)≤D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀x∈portLow Q D,GoodPort Q x) : Q=⊤ ∧ Nat.card X≤D := by
  have noEven (h : Even D) : False := by
    have a := Nat.odd_iff.mp odd
    have b := Nat.even_iff.mp h
    omega
  rcases good_port_classification Q D cap crit good with regular|⟨clique,_,size⟩|split
  · have order := factorCritical_order_rank Q crit (Classical.choice ‹Nonempty X›)
    have oddN : Odd (Nat.card X) := ⟨matchingEdges Q,by omega⟩
    exact (noEven (regular_even_on_odd Q D oddN regular)).elim
  · exact ⟨clique,size⟩
  · exact (noEven split.even).elim

theorem region_good_piece_odd_clique (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D)
    (odd : Odd D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (c : (G.induce K.barrierᶜ).ConnectedComponent)
    (good : ∀x∈portLow ((G.induce K.barrierᶜ).induce c.supp) D,
      GoodPort ((G.induce K.barrierᶜ).induce c.supp) x) :
    (G.induce K.barrierᶜ).induce c.supp=⊤ ∧ Nat.card c.supp≤D := by
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  apply odd_good_component_is_small_clique _ D odd _ (K.critical c).2 good
  intro x
  exact (induced_neighbor_count_le _ c.supp x).trans
    ((induced_neighbor_count_le G K.barrierᶜ x.val).trans (cap _))

#print axioms region_good_piece_odd_clique
end JSP452Audit.StarHost
