import FactorCriticalReserve
namespace JSP452Audit.StarHost
open SimpleGraph
/-- A real perfect matching off a vertex exhibits the exact host order and rank. -/
theorem factorCritical_order_rank {X : Type*} [Finite X] (G : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion G) (v : X) : Nat.card X = 2*matchingEdges G+1 := by
  obtain ⟨M,hM⟩ := crit v
  obtain ⟨P,hP,verts,rank⟩ := lift_perfect_off_vertex_maximum G v M hM
  have rem : {x : X | x≠v} = ({v} : Set X)ᶜ := by ext; simp
  have count := matching_vertices_eq_twice_edges hP
  rw [verts,rem,Set.ncard_compl,Set.ncard_singleton,rank] at count
  have pos : 0<Nat.card X := by
    let _ : Nonempty X := ⟨v⟩
    exact Nat.card_pos
  omega

theorem factorCritical_missed_card {X : Type*} [Finite X] (G : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion G) (v : X)
    (M : G.Subgraph) (hm : M.IsMatching) (max : M.edgeSet.ncard=matchingEdges G) :
    M.vertsᶜ.ncard=1 := by
  have order := factorCritical_order_rank G crit v
  rw [Set.ncard_compl,matching_vertices_eq_twice_edges hm,max,order]
  omega

/-- On an actual nonempty regular factor-critical graph the unavoidable full-degree
exposure is exactly one. It never grows with the width of a request. -/
theorem regular_factorCritical_exposure {X : Type*} [Finite X] (G : SimpleGraph X)
    (crit : PerfectAfterEveryDeletion G) (v : X) (D : ℕ)
    (reg : ∀ x, Nat.card (G.neighborSet x)=D) : minimumExposure G D=1 := by
  obtain ⟨M,hm,max,att⟩ := minimumExposure_attained G D
  have all : exposedFull G M D = M.vertsᶜ := by
    ext x
    change (x∉M.verts ∧ Nat.card (G.neighborSet x)=D) ↔ x∉M.verts
    simp [reg]
  rw [← att,all]
  exact factorCritical_missed_card G crit v M hm max

/-- A factor-critical original forced host at the critical degree has exactly
one highest column, whatever the multiplicities of its two input lists. -/
theorem factorCritical_forcing_width_one {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (v : X) (r : ℕ) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (live : 0<rowCount s t r)
    (bound : ∀ x, Nat.card (G.neighborSet x) ≤ diagonal n m (r+2)-1)
    (crit : PerfectAfterEveryDeletion G) : highestWidth n m r=1 := by
  have ⟨lo,hi⟩ := row_minimum_exposure hs ht n m hn hm pn pm G r live row bound
  have eq := regular_factorCritical_exposure G crit v _ (factorCritical_forcing_row_regular hs ht n m hn hm pn pm G r row live bound crit)
  omega
#print axioms factorCritical_order_rank
#print axioms regular_factorCritical_exposure
#print axioms factorCritical_forcing_width_one
end JSP452Audit.StarHost