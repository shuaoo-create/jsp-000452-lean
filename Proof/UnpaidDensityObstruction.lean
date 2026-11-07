import DominatingPairDensity
namespace JSP452Audit.StarHost
open SimpleGraph
variable {X : Type*} [Finite X]

/-- An actual component still violating the reserve must have at least D+5
vertices. Its complement degree also meets the two-step counting bound. -/
theorem unpaid_component_density_obstruction (G : SimpleGraph X) (D k : ℕ)
    (large : 3≤D) (cap : ∀x,Nat.card (G.neighborSet x)≤D) (c : G.ConnectedComponent)
    (unpaid : envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D) :
    let n := Nat.card c.supp
    let r := n-1-D
    D+5≤n ∧ n-1≤r*(r-1) := by
  intro n r
  let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
  obtain ⟨reg,crit,evenD,four,_⟩ := unpaid_component_obstruction G D k large cap c unpaid
  have cr (x : c.supp) := (component_degree_eq G c x).trans (reg x)
  have quadratic : n-1≤r*(r-1) := by
    by_contra! dense
    exact (Nat.not_lt_of_ge (dense_regular_component_pays c.toSimpleGraph D k four cr crit dense)) unpaid
  have x : c.supp := Classical.choice ‹Nonempty c.supp›
  have d_le_n : D≤n := by
    have small := Set.ncard_le_ncard (Set.subset_univ (c.toSimpleGraph.neighborSet x))
    rw [Set.ncard_univ,←Nat.card_coe_set_eq,cr] at small
    exact small
  have order := factorCritical_order_rank c.toSimpleGraph crit x
  obtain ⟨j,even⟩ := evenD
  change n=2*matchingEdges c.toSimpleGraph+1 at order
  have limit : D+5≤n := by
    by_contra! lt
    have opts : r=0 ∨ r=2 := by dsimp [r]; omega
    rcases opts with e|e <;> rw [e] at quadratic <;> norm_num at quadratic <;> omega
  exact ⟨limit,quadratic⟩

theorem global_unpaid_has_large_sparse_component (G : SimpleGraph X) (D k : ℕ)
    (large : 3≤D) (cap : ∀x,Nat.card (G.neighborSet x)≤D)
    (unpaid : envelopeReserve G k<minimumExposure G D) :
    ∃ c : G.ConnectedComponent, envelopeReserve c.toSimpleGraph k<minimumExposure c.toSimpleGraph D ∧
      D+5≤Nat.card c.supp ∧
        Nat.card c.supp-1≤(Nat.card c.supp-1-D)*(Nat.card c.supp-1-D-1) := by
  obtain ⟨c,fail⟩ := exists_unpaid_original_component G D k unpaid
  exact ⟨c,fail,unpaid_component_density_obstruction G D k large cap c fail⟩

#print axioms unpaid_component_density_obstruction
#print axioms global_unpaid_has_large_sparse_component
end JSP452Audit.StarHost
