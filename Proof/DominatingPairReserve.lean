import DominatingPairBudget
import GlobalComponentReserve
import IndependentLayerPrice
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- The two-point budget certificate pays every regular critical host with an
independent triple. No exhaustive equimatchable classification is used. -/
theorem regular_dominating_pair_base_reserve [Nonempty X] (Q : SimpleGraph X) (D k : ℕ) (large : 4≤D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (I : Set X) (three : I.ncard=3) (ind : Q.IsIndepSet I)
    (x y : X) (ne : x≠y)
    (dominate : ∀v,v≠x → v≠y → Q.Adj v x ∨ Q.Adj v y) :
    1≤baseReserve Q k := by
  have order := factorCritical_order_rank Q crit (Classical.choice ‹Nonempty X›)
  have odd : Odd (Nat.card X) := ⟨matchingEdges Q,by omega⟩
  have cheap := dominating_pair_budget Q D large odd reg x y ne dominate
  have nonempty : I.Nonempty := Set.nonempty_of_ncard_ne_zero (by omega)
  have price := independent_layer_two_vertex_certificate Q D (by omega) reg crit I nonempty ind cheap
  have truncate := baseReserve_le_truncation Q D k (fun v => (reg v).le)
  omega

/-- Small independence and a real dominating pair together cover all
independence numbers at every truncation height on this host. -/
theorem regular_dominating_pair_pays [Nonempty X] (Q : SimpleGraph X) (D k : ℕ) (large : 4≤D)
    (reg : ∀v,Nat.card (Q.neighborSet v)=D) (crit : PerfectAfterEveryDeletion Q)
    (x y : X) (ne : x≠y)
    (dominate : ∀v,v≠x → v≠y → Q.Adj v x ∨ Q.Adj v y) :
    minimumExposure Q D≤envelopeReserve Q k := by
  by_cases small : NoIndependentTriple Q
  · exact small_alpha_component_pays Q D k (by omega) reg crit small
  obtain ⟨I,three,ind⟩ := independent_triple_vertex_set Q small
  rw [regular_factorCritical_exposure Q crit (Classical.choice ‹Nonempty X›) D reg]
  exact (regular_dominating_pair_base_reserve Q D k large reg crit I three ind x y ne dominate).trans
    (envelope_reserve_account Q k).2

/-- Any remaining unpaid actual component has no dominating pair at all.
Its labels and degrees are the original graph's; this is not an isomorphism
classification and does not assume that every component has such a pair. -/
theorem unpaid_component_has_no_dominating_pair (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D) (c : G.ConnectedComponent)
    (unpaid : envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D) :
    ∀x y:c.supp,x≠y →
      ¬(∀v:c.supp,v≠x → v≠y → c.toSimpleGraph.Adj v x ∨ c.toSimpleGraph.Adj v y) := by
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  obtain ⟨reg,crit,_,four,_⟩ := unpaid_component_obstruction G D k large cap c unpaid
  intro x y ne dominate
  have pay := regular_dominating_pair_pays c.toSimpleGraph D k four
    (fun v => (component_degree_eq G c v).trans (reg v)) crit x y ne dominate
  exact (Nat.not_lt_of_ge pay) unpaid

/-- A concrete sufficient structural condition: each original regular critical
component either has small independence or has two actual dominating labels. -/
theorem reserve_of_regular_small_or_dominating (G : SimpleGraph X) (D k : ℕ) (large : 3≤D)
    (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (resolve : ∀c:G.ConnectedComponent,
      (∀x:c.supp,Nat.card (G.neighborSet x.val)=D) →
      PerfectAfterEveryDeletion c.toSimpleGraph →
      NoIndependentTriple c.toSimpleGraph ∨
      ∃x y:c.supp,x≠y ∧
        ∀v:c.supp,v≠x → v≠y → c.toSimpleGraph.Adj v x ∨ c.toSimpleGraph.Adj v y) :
    minimumExposure G D≤envelopeReserve G k := by
  by_contra bad
  obtain ⟨c,unpaid⟩ := exists_unpaid_original_component G D k (Nat.lt_of_not_ge bad)
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  obtain ⟨reg,crit⟩ := unpaid_component_regular G D k (by omega) cap c unpaid
  rcases resolve c reg crit with small|⟨x,y,ne,dominate⟩
  · have pay := small_alpha_component_pays c.toSimpleGraph D k large
      (fun v => (component_degree_eq G c v).trans (reg v)) crit small
    exact (Nat.not_lt_of_ge pay) unpaid
  · exact unpaid_component_has_no_dominating_pair G D k large cap c unpaid x y ne dominate

#print axioms reserve_of_regular_small_or_dominating
#print axioms regular_dominating_pair_base_reserve
#print axioms regular_dominating_pair_pays
#print axioms unpaid_component_has_no_dominating_pair
end JSP452Audit.StarHost
