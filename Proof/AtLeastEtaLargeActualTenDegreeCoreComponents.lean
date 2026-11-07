import TheSameSurvivingStarsOnTheRootRetainingTenDegreeGraph
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem twice_edges_le_ten_order {X:Type u} [Finite X] (G:SimpleGraph X) (cap:∀v,Nat.card (G.neighborSet v)≤10) :
    2*G.edgeSet.ncard≤10*Nat.card X := by
  have fee := degree_sum_complement G Set.univ
  have empty : originalDegreeSum G (Set.univ:Set X)ᶜ=0 := by simp [originalDegreeSum]
  have bound := degree_sum_le_cap G Set.univ 10 (fun x _ => cap x)
  rw [empty,Nat.add_zero] at fee
  rw [Set.ncard_univ,fee] at bound;exact bound

theorem small_component_owes_ten (n k:ℕ) (positive:0<n) (small:n≤10) (simple:2*k≤n*(n-1)) :
    2*k+10≤10*n := by interval_cases n <;> omega

namespace TenBlockPartition
variable {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenBlockPartition G)
abbrev coreGraph := G.induce K.core
def largeComponents : Set K.coreGraph.ConnectedComponent := {c|11≤Nat.card c.supp}

theorem component_totals [Fintype K.coreGraph.ConnectedComponent] :
    (∑c:K.coreGraph.ConnectedComponent,Nat.card c.supp)=K.core.ncard ∧
    (∑c:K.coreGraph.ConnectedComponent,matchingEdges c.toSimpleGraph)=K.capacity ∧
    Fintype.card K.coreGraph.ConnectedComponent=K.roots.ncard+K.eta := by
  have size : (∑c:K.coreGraph.ConnectedComponent,Nat.card c.supp)=K.core.ncard := by
    rw [←Nat.card_sigma];exact Nat.card_congr (Equiv.sigmaFiberEquiv K.coreGraph.connectedComponentMk)
  have ranks := (host_component_totals K.coreGraph).2.1
  have eq (c:K.coreGraph.ConnectedComponent) : Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 :=
    factorCritical_order_rank c.toSimpleGraph (K.critical c).2 c.nonempty_supp.to_subtype.some
  have total := Finset.sum_congr (s₁:=Finset.univ) rfl (fun c _ => eq c)
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id,Nat.mul_one,
    size,←ranks] at total
  have order : K.core.ncard=2*K.capacity+K.roots.ncard+K.eta := K.order
  change K.core.ncard=2*K.capacity+_ at total
  exact ⟨size,ranks.symm,by omega⟩

theorem many_large_components (cap:∀v,Nat.card (G.neighborSet v)≤10) (small:K.epsilon≤2) :
    K.eta≤K.largeComponents.ncard ∧ 5*K.largeComponents.ncard≤K.capacity := by
  classical
  let C := K.coreGraph
  let _ := Fintype.ofFinite C.ConnectedComponent
  let B := K.largeComponents
  obtain ⟨sumN,sumR,number⟩ := K.component_totals
  have edges := (host_component_totals C).1
  have point (c:C.ConnectedComponent) :
      2*c.toSimpleGraph.edgeSet.ncard+10≤10*Nat.card c.supp+(if c∈B then 10 else 0) := by
    by_cases big:c∈B
    · rw [if_pos big]
      have loc (v:c.supp) : Nat.card (c.toSimpleGraph.neighborSet v)≤10 := (component_degree_eq C c v).le.trans
        ((induced_neighbor_count_le G K.core v.val).trans (cap v.val.val))
      have bound := twice_edges_le_ten_order c.toSimpleGraph loc
      change 2*c.toSimpleGraph.edgeSet.ncard≤10*Nat.card c.supp at bound;omega
    · rw [if_neg big,Nat.add_zero]
      change ¬11≤Nat.card c.supp at big
      let _ : Nonempty c.supp := c.nonempty_supp.to_subtype
      exact small_component_owes_ten _ _ Nat.card_pos (by omega) (twice_edges_le_simple_order c.toSimpleGraph)
  have mass (c:C.ConnectedComponent) : (if c∈B then 5 else 0)≤matchingEdges c.toSimpleGraph := by
    split_ifs with big
    · change 11≤Nat.card c.supp at big
      have eq := factorCritical_order_rank c.toSimpleGraph (K.critical c).2 c.nonempty_supp.to_subtype.some
      change Nat.card c.supp=2*matchingEdges c.toSimpleGraph+1 at eq;omega
    · omega
  have indicator (k:ℕ) : (∑c:C.ConnectedComponent,if c∈B then k else 0)=k*B.ncard := by
    have count : (Finset.univ.filter (fun c:C.ConnectedComponent => c∈B)).card=B.ncard := by
      rw [←Set.ncard_coe_finset];congr 1;ext c;simp
    rw [←Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,count,Nat.mul_comm]
  have account := Finset.sum_le_sum (s:=(Finset.univ:Finset C.ConnectedComponent)) (fun c _ => point c)
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib,←Finset.mul_sum,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,
    nsmul_eq_mul,Nat.cast_id,indicator,←edges] at account
  change 2*C.edgeSet.ncard+Fintype.card C.ConnectedComponent*10≤10*(∑c:C.ConnectedComponent,Nat.card c.supp)+10*B.ncard at account
  rw [sumN,number] at account
  have toll := (K.edge_fees cap).2.2.1
  change 2*C.edgeSet.ncard+K.epsilon=20*K.capacity+10*K.eta+_+_+_ at toll
  have order : K.core.ncard=2*K.capacity+K.roots.ncard+K.eta := K.order
  have count := Finset.sum_le_sum (s:=(Finset.univ:Finset C.ConnectedComponent)) (fun c _ => mass c)
  rw [indicator,sumR] at count
  change K.eta≤B.ncard ∧ 5*B.ncard≤K.capacity
  omega
end TenBlockPartition
#print axioms small_component_owes_ten
#print axioms TenBlockPartition.component_totals
#print axioms TenBlockPartition.many_large_components
end JSP452Audit.StarHost
