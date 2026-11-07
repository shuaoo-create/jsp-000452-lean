import ComponentThresholdSlotCapacity
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Positive component surplus is at most D/2 and requires order at
least D+1. Such a component necessarily loses at least one slot when
one compares two-leaf-star capacity with matching capacity. -/
theorem component_surplus_two_slots {X : Type*} [Finite X] [Nonempty X] (Q : SimpleGraph X)
    (D : ℕ) (degree : 3≤D) (crit : PerfectAfterEveryDeletion Q)
    (cap : ∀x,Nat.card (Q.neighborSet x)≤D) :
    2*edgeSurplus Q D+(D:ℤ)*(Nat.card X/3:ℕ)≤(D:ℤ)*(matchingEdges Q:ℤ) := by
  have ord := factorCritical_order_rank Q crit (Classical.arbitrary X)
  by_cases pos : 0<edgeSurplus Q D
  · obtain ⟨big,hi,_⟩ := positive_core_caps Q crit D cap pos
    have gap : Nat.card X/3+1≤matchingEdges Q := by omega
    have scaled := Nat.mul_le_mul_left D gap
    rw [Nat.mul_add,Nat.mul_one] at scaled
    have cost : (D:ℤ)*(Nat.card X/3:ℕ)+(D:ℤ)≤(D:ℤ)*(matchingEdges Q:ℤ) := by exact_mod_cast scaled
    omega
  · have slots : Nat.card X/3≤matchingEdges Q := by omega
    have scaled : (D:ℤ)*(Nat.card X/3:ℕ)≤(D:ℤ)*(matchingEdges Q:ℤ) := by
      exact_mod_cast Nat.mul_le_mul_left D slots
    omega

theorem ordinary_slot_budget {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) (K : DegreeRegion G D)
    (degree : 3≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    D*minimumExposure G D+rootShortfall G K.roots D+2*(G.induce K.roots).edgeSet.ncard+
      crossCount G K.roots K.rest+D*componentSlots (G.induce K.core) 2 ≤ D*matchingEdges (G.induce K.core) := by
  classical
  let H := G.induce K.core
  let _ := Fintype.ofFinite H.ConnectedComponent
  have each (c:H.ConnectedComponent) :
      2*edgeSurplus c.toSimpleGraph D+(D:ℤ)*(Nat.card c.supp/3:ℕ)≤(D:ℤ)*(matchingEdges c.toSimpleGraph:ℤ) := by
    let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
    exact component_surplus_two_slots c.toSimpleGraph D degree (ordinary_core_components_critical G K c)
      (fun x => (induced_neighbor_count_le H c.supp x).trans ((induced_neighbor_count_le G K.core x.val).trans (cap _)))
  have total := Finset.sum_le_sum (s:=Finset.univ) (fun c _ => each c)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,←Finset.mul_sum,←Nat.cast_sum,←Nat.cast_sum] at total
  have sums := surplus_component_finset H Finset.univ D
  have univ : {x | H.connectedComponentMk x∈(Finset.univ:Finset H.ConnectedComponent)}=Set.univ := by ext;simp
  rw [univ,edgeSurplus_iso (induceUnivIso H)] at sums
  change edgeSurplus H D=∑c:H.ConnectedComponent,edgeSurplus c.toSimpleGraph D at sums
  change 2*(∑c:H.ConnectedComponent,edgeSurplus c.toSimpleGraph D)+
    (D:ℤ)*(componentSlots H 2:ℤ)≤(D:ℤ)*(∑c:H.ConnectedComponent,matchingEdges c.toSimpleGraph:ℕ) at total
  rw [←sums,←(component_rank_budget_gluing H).1] at total
  have fee := K.weight_identity cap
  change 2*edgeSurplus H D=_ at fee
  rw [fee] at total
  exact_mod_cast total

theorem original_two_threshold_slot_guard {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (hn : Antitone n) (degree : 3≤D)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) :
    let H := G.induce K.core
    let W := componentBudget H n
    D*minimumExposure G D+rootShortfall G K.roots D+D*originalThresholdCount n 2≤
      D*(matchingEdges H+originalThresholdCount (W.entries n) 2) := by
  intro H W
  have slots := ordinary_slot_budget G D K degree cap
  have count := actual_threshold_capacity H n hn 2
  have scaled := Nat.mul_le_mul_left D count
  rw [Nat.mul_add] at scaled ⊢
  change D*originalThresholdCount n 2≤D*originalThresholdCount (W.entries n) 2+D*componentSlots H 2 at scaled
  change D*minimumExposure G D+rootShortfall G K.roots D+2*(G.induce K.roots).edgeSet.ncard+
    crossCount G K.roots K.rest+D*componentSlots H 2≤D*matchingEdges H at slots
  omega

#print axioms component_surplus_two_slots
#print axioms ordinary_slot_budget
#print axioms original_two_threshold_slot_guard
end JSP452Audit.StarHost
