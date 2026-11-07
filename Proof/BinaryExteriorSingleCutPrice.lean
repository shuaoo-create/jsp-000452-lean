import StrictBinaryZeroOffsetEntry
namespace JSP452Audit.StarHost
open SimpleGraph

theorem component_slot_vertex_price {X : Type*} [Finite X] (H : SimpleGraph X) (j : ℕ) :
    (j+1)*componentSlots H j≤Nat.card X := by
  classical
  let _ := Fintype.ofFinite H.ConnectedComponent
  have space : (∑c:H.ConnectedComponent,Nat.card c.supp)=Nat.card X := by
    rw [←Nat.card_sigma];exact Nat.card_congr (Equiv.sigmaFiberEquiv H.connectedComponentMk)
  have each (c:H.ConnectedComponent) : (j+1)*(Nat.card c.supp/(j+1))≤Nat.card c.supp := by
    simpa only [Nat.mul_comm (j+1)] using Nat.div_mul_le_self (Nat.card c.supp) (j+1)
  change (j+1)*(∑c:H.ConnectedComponent,Nat.card c.supp/(j+1))≤Nat.card X
  rw [Finset.mul_sum,←space]
  exact Finset.sum_le_sum (fun c _ => each c)

theorem nonunit_slot_volume {s D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (hn : Antitone n) :
    let H := G.induce K.core
    let c := originalThresholdCount ((componentBudget H n).entries n) 2
    3*originalThresholdCount n 2≤3*c+2*matchingEdges H+K.roots.ncard+minimumExposure G D := by
  intro H c
  have slots := actual_threshold_capacity H n hn 2
  change originalThresholdCount n 2≤c+componentSlots H 2 at slots
  have space := component_slot_vertex_price H 2
  change 3*componentSlots H 2≤Nat.card ↥K.core at space
  rw [Nat.card_coe_set_eq] at space
  have ord := K.core_order
  change K.core.ncard=2*matchingEdges H+K.roots.ncard+minimumExposure G D at ord
  omega

/-- At zero offset and with a binary opponent, cutting even numbers
inside the odd components bounds the one-exterior loss by half the
original star count at that height. -/
theorem one_exterior_even_cut_bound {s t D : ℕ} {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (ht : 0<t) (row : ForcingRow G s t (padDemand n) (padDemand m) 0) (embed : t≤matchingEdges (G.induce K.core))
    (binary : m ⟨0,ht⟩=2) (j : ℕ) (pos : 0<j) :
    let f := originalThresholdCount n j
    2*(f+t-1)≤2*(K.roots.ncard+matchingEdges (G.induce K.core)+uniformEnvelope (G.induce K.rest) j)+f := by
  intro f
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  have each (i : Fin t) : (m i-1)/2=0 := by
    have small := hm (show (⟨0,ht⟩ : Fin t)≤ i from Nat.zero_le _);omega
  have no : (∑i,(m i-1)/2)=0 := by simp [each]
  have fits : t+∑i,(m i-1)/2≤μ := by rwa [no,Nat.add_zero]
  obtain ⟨v,actual⟩ := exact_axis_repair_inventory G K n m hn hm pn pm ht row fits
  let w := μ+1-t
  let V := halfOrderBudget m (μ-w)
  have rep := actual j pos
  rw [no,Nat.add_zero] at rep v
  change 0<V.len at v
  change 2*w<f → f-2*w+V.len-1-(0+a)≤uniformEnvelope (G.induce K.rest) j ∧ _ at rep
  change t≤μ at embed
  have key : w+t=μ+1 := by dsimp [w];omega
  change 2*(f+t-1)≤2*(a+μ+uniformEnvelope (G.induce K.rest) j)+f
  by_cases many : 2*w<f
  · have pay := (rep many).1;omega
  · omega

#print axioms component_slot_vertex_price
#print axioms nonunit_slot_volume
#print axioms one_exterior_even_cut_bound
end JSP452Audit.StarHost