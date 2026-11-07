import GoodPortParts
import EquimatchableReserve
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]
theorem good_port_order_split (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀v, Nat.card (Q.neighborSet v) ≤ D) :
    (portFull Q D).ncard + (portLow Q D).ncard = Nat.card X := by
  have compl : (portFull Q D)ᶜ = portLow Q D := by
    ext x
    change (¬ Nat.card (Q.neighborSet x)=D) ↔ Nat.card (Q.neighborSet x)<D
    specialize cap x; omega
  simpa [compl] using Set.ncard_add_ncard_compl (portFull Q D)

theorem full_port_clique_card (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀v, Nat.card (Q.neighborSet v) ≤ D)
    (clique : Q.IsClique (portFull Q D))
    (join : ∀x∈portFull Q D,∀y∈portLow Q D,Q.Adj x y)
    (v : X) (hv : v∈portFull Q D) : Nat.card X = D + 1 := by
  have neigh : Q.neighborSet v = ({v} : Set X)ᶜ := by
    ext x
    change Q.Adj v x ↔ x ≠ v
    constructor
    · exact fun edge => edge.ne.symm
    · intro different
      by_cases full : x ∈ portFull Q D
      · exact clique hv full different.symm
      · have H := cap x
        change ¬ Nat.card (Q.neighborSet x)=D at full
        exact join v hv x (show Nat.card (Q.neighborSet x)<D by omega)
  have full := hv
  change Nat.card (Q.neighborSet v) = D at full
  rw [Nat.card_coe_set_eq,neigh,Set.ncard_compl,Set.ncard_singleton] at full
  let _ : Nonempty X := ⟨v⟩
  have pos := Nat.card_pos (α:=X)
  omega

theorem good_port_split_arithmetic (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀v, Nat.card (Q.neighborSet v) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀v∈portLow Q D,GoodPort Q v) (v : X) (hv : v∈portFull Q D) :
    ∃ m0 : ℕ, (portFull Q D).ncard=2*m0+(portLow Q D).ncard+1 := by
  have split := good_port_order_split Q D cap
  have odd := factorCritical_order_rank Q crit v
  have room := low_add_one_le_full Q D cap crit good v hv
  exact ⟨matchingEdges Q - (portLow Q D).ncard,by omega⟩

#print axioms full_port_clique_card
#print axioms good_port_split_arithmetic
end JSP452Audit.StarHost
