import TwoWholeComponentGap
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_spare_component_supply {F:StrictFamily.{u}} (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    ∃I:Set F.X,F.G.IsIndepSet I ∧ (∀v∈I,Nat.card (F.G.neighborSet v)=6) ∧ (∀c∉T,Disjoint c.supp I) ∧
      (∑c∈T,matchingEdges c.toSimpleGraph)≤3*I.ncard := by
  classical
  have orig := (minimal_rank_exact_source F paid).2.2.2.1
  obtain ⟨J,inside,ind,room⟩ := independent_union_of_components F.G 6 (fun v => (orig v).trans_eq six) (↑T:Set F.G.ConnectedComponent)
  have per (c:↥T) : Nat.card c.val.supp-1=2*matchingEdges c.val.toSimpleGraph := by
    have eq := (strict_six_true_component_capacity F paid six c.val (actual c.val c.property)).2.1
    omega
  change (∑c:↥T,(Nat.card c.val.supp-1))≤6*J.ncard at room
  simp only [per,←Finset.mul_sum] at room
  have sum : (∑c:↥T,matchingEdges c.val.toSimpleGraph)=∑c∈T,matchingEdges c.toSimpleGraph :=
    Finset.sum_coe_sort T (fun c => matchingEdges c.toSimpleGraph)
  rw [sum] at room
  refine ⟨J,ind,?_,?_,by omega⟩
  · intro v hv
    exact (actual _ (inside v hv)).2 v rfl
  · intro c notT
    exact Set.disjoint_left.mpr fun x hc hj => notT ((show F.G.connectedComponentMk x=c from hc) ▸ inside x hj)

theorem strict_six_single_spare_guard {F:StrictFamily.{u}} (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (low:highestWidth F.n F.m F.r≤3)
    (c:F.G.ConnectedComponent) (member:c∈oddRegularComponents F.G 6) (T:Finset F.G.ConnectedComponent)
    (actual:∀w∈T,w∈oddRegularComponents F.G 6) (outside:c∉T) :
    (∑w∈T,matchingEdges w.toSimpleGraph)+3*(F.r+2)≤3*matchingEdges c.toSimpleGraph := by
  obtain ⟨I,ind,full,apart,capacity⟩ := six_spare_component_supply paid six T actual
  let e : Fin 1 ↪ F.G.ConnectedComponent := ⟨fun _ => c,fun _ _ _ => Subsingleton.elim _ _⟩
  have bound : F.r+I.ncard+1<matchingEdges c.toSimpleGraph := by
    by_contra! small
    have menu := split_capacities_of_small (fun i:Fin 1 => matchingEdges (e i).toSimpleGraph) (F.r+I.ncard) (fun _ => small)
    have contradiction := strict_six_no_full_degree_menu F paid six e (fun _ => member) I menu ind full (fun _ => apart c outside)
    rw [Fintype.card_fin] at contradiction
    omega
  omega

theorem strict_six_two_spare_guard {F:StrictFamily.{u}} (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (e:Fin 2 ↪ F.G.ConnectedComponent)
    (actual:∀i,e i∈oddRegularComponents F.G 6) (T:Finset F.G.ConnectedComponent)
    (spare:∀w∈T,w∈oddRegularComponents F.G 6) (outside:∀i,e i∉T)
    (ord:matchingEdges (e 0).toSimpleGraph≤matchingEdges (e 1).toSimpleGraph) :
    let a := matchingEdges (e 0).toSimpleGraph
    let b := matchingEdges (e 1).toSimpleGraph
    (∑w∈T,matchingEdges w.toSimpleGraph)+3*(F.r+2)≤3*max a (b-a) := by
  intro a b
  obtain ⟨I,ind,full,apart,capacity⟩ := six_spare_component_supply paid six T spare
  have bound := strict_pair_gap_needs_paid_exterior paid six e actual I ind full (fun i => apart (e i) (outside i)) ord
  change F.r+I.ncard+1<max a (b-a) at bound
  omega

#print axioms six_spare_component_supply
#print axioms strict_six_single_spare_guard
#print axioms strict_six_two_spare_guard
end JSP452Audit.StarHost
