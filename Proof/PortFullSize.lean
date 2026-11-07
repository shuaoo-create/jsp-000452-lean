import GoodPortParts
import TightDeletesRank
import RegularCriticalHost

namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

omit [Finite X] in
theorem compl_portLow (Q : SimpleGraph X) (D : ℕ) (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) :
    (portLow Q D)ᶜ = portFull Q D := by
  ext x
  change (¬Nat.card (Q.neighborSet x)<D) ↔ Nat.card (Q.neighborSet x)=D
  have := cap x
  omega

/-- Deleting all low vertices loses at most their number in matching rank. -/
theorem portFull_matching_floor (Q : SimpleGraph X) (D m0 : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q) (v : X)
    (shape : (portFull Q D).ncard = 2*m0+(portLow Q D).ncard+1) :
    m0 ≤ matchingEdges (Q.induce (portFull Q D)) := by
  have rank := factorCritical_order_rank Q crit v
  have cut := matching_rank_le_cut_add Q (portLow Q D)
  have count := Set.ncard_add_ncard_compl (portLow Q D)
  rw [compl_portLow Q D cap] at cut count
  omega

/-- A low vertex is joined to every full vertex and has degree strictly below D. -/
theorem portFull_card_lt_of_low (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ y ∈ portLow Q D, GoodPort Q y) (lows : (portLow Q D).Nonempty) :
    (portFull Q D).ncard < D := by
  obtain ⟨y,hy⟩ := lows
  have le : portFull Q D ⊆ Q.neighborSet y := fun _ hx => (full_adj_good_low Q D cap crit good hx hy).symm
  exact (Set.ncard_le_ncard le).trans_lt hy

/-- With only one or two low vertices every full vertex has all possible neighbors. -/
theorem portFull_complete_few_low (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ y ∈ portLow Q D, GoodPort Q y)
    (positive : 0 < (portLow Q D).ncard) (few : (portLow Q D).ncard ≤ 2) :
    Q.induce (portFull Q D) = ⊤ := by
  have floor := portFull_card_lt_of_low Q D cap crit good ((Set.ncard_pos (s := portLow Q D)).mp positive)
  have count := Set.ncard_add_ncard_compl (portLow Q D)
  rw [compl_portLow Q D cap] at count
  apply top_unique
  intro a b distinct
  have sub : Q.neighborSet a.val ⊆ ({a.val} : Set X)ᶜ := by
    intro y edge eq
    exact edge.ne (Set.mem_singleton_iff.mp eq).symm
  have full : (Q.neighborSet a.val).ncard = D := a.property
  have surj : Q.neighborSet a.val = ({a.val} : Set X)ᶜ := by
    apply Set.eq_of_subset_of_ncard_le sub
    rw [Set.ncard_compl,Set.ncard_singleton,full]
    omega
  change b.val ∈ Q.neighborSet a.val
  rw [surj]
  exact fun eq => distinct (Subtype.ext (Set.mem_singleton_iff.mp eq).symm)

#print axioms portFull_matching_floor
#print axioms portFull_card_lt_of_low
#print axioms portFull_complete_few_low
end JSP452Audit.StarHost
