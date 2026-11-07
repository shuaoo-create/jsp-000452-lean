import FullPortClique
import PortLowIndependent
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The split graph on the original vertex labels. In particular there is
no edge between two low ports, and every full vertex is universal. -/
structure GoodPortSplit (Q : SimpleGraph X) (D : ℕ) : Prop where
  even : Even D
  order : Nat.card X = D+1
  low_count : 2 ≤ (portLow Q D).ncard
  room : (portLow Q D).ncard+1 ≤ (portFull Q D).ncard
  join : ∀x y, Q.Adj x y ↔ x≠y ∧ (x∈portFull Q D ∨ y∈portFull Q D)

theorem mixed_good_port_split (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x∈portLow Q D,GoodPort Q x) (v : X) (hv : v∈portFull Q D)
    (lows : (portLow Q D).Nonempty) : GoodPortSplit Q D := by
  have cl := full_set_of_mixed_ports_is_clique Q D cap crit good v hv lows
  have joined : ∀x∈portFull Q D,∀y∈portLow Q D,Q.Adj x y :=
    fun _ hx _ hy => full_adj_good_low Q D cap crit good hx hy
  have room := low_add_one_le_full Q D cap crit good v hv
  have rank := factorCritical_order_rank Q crit v
  have ord := full_port_clique_card Q D cap cl joined v hv
  have n := good_port_order_split Q D cap
  have ltD := portFull_card_lt_of_low Q D cap crit good lows
  have odd : Odd (Nat.card X) := ⟨matchingEdges Q,by omega⟩
  have independent := portLow_independent Q D cap cl joined room odd good
  have low_of_not {x : X} (miss : x∉portFull Q D) : x∈portLow Q D := by
    change ¬ Nat.card (Q.neighborSet x)=D at miss
    change Nat.card (Q.neighborSet x)<D
    specialize cap x; omega
  have universal {x y : X} (full : x∈portFull Q D) (different : x≠y) : Q.Adj x y := by
    by_cases hy : y∈portFull Q D
    · exact cl full hy different
    · exact joined x full y (low_of_not hy)
  refine ⟨⟨matchingEdges Q,by omega⟩,ord,by omega,room,?_⟩
  intro x y
  constructor
  · intro edge
    refine ⟨edge.ne,?_⟩
    by_contra none
    push Not at none
    exact independent (low_of_not none.1) (low_of_not none.2) edge.ne edge
  · rintro ⟨different,hx|hy⟩
    · exact universal hx different
    · exact (universal hy different.symm).symm

/-- Full good-port trichotomy including the no-low and no-full branches.
The complete branch has odd order bounded by D. -/
theorem good_port_classification [Nonempty X] (Q : SimpleGraph X) (D : ℕ)
    (cap : ∀ x, Nat.card (Q.neighborSet x) ≤ D) (crit : PerfectAfterEveryDeletion Q)
    (good : ∀ x∈portLow Q D,GoodPort Q x) :
    (∀x,Nat.card (Q.neighborSet x)=D) ∨
      (Q=⊤ ∧ Odd (Nat.card X) ∧ Nat.card X ≤ D) ∨ GoodPortSplit Q D := by
  classical
  by_cases lows : (portLow Q D).Nonempty
  · by_cases full : (portFull Q D).Nonempty
    · obtain ⟨v,hv⟩ := full
      exact Or.inr (Or.inr (mixed_good_port_split Q D cap crit good v hv lows))
    · have allLow : ∀x,x∈portLow Q D := by
        intro x
        have h : x∉portFull Q D := fun hx => full ⟨x,hx⟩
        change ¬ Nat.card (Q.neighborSet x)=D at h
        change Nat.card (Q.neighborSet x)<D
        specialize cap x; omega
      have top := all_low_ports_complete Q D crit allLow good
      obtain ⟨v,hv⟩ := lows
      have rank := factorCritical_order_rank Q crit v
      refine Or.inr (Or.inl ⟨top,⟨matchingEdges Q,by omega⟩,?_⟩)
      change Nat.card (Q.neighborSet v)<D at hv
      have neigh : Q.neighborSet v=({v}:Set X)ᶜ := by
        ext w
        rw [top]
        exact ne_comm
      rw [Nat.card_coe_set_eq,neigh,Set.ncard_compl,Set.ncard_singleton] at hv
      omega
  · left
    intro x
    have h : x∉portLow Q D := fun hx => lows ⟨x,hx⟩
    change ¬ Nat.card (Q.neighborSet x)<D at h
    specialize cap x; omega

#print axioms mixed_good_port_split
#print axioms good_port_classification
end JSP452Audit.StarHost
