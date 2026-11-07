import StrictExteriorHistoryCutBounds
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_chosen_slot_totals (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    let P := matchingEdges (F.G.induce (componentVertices F.G T))
    3*chosenSlots F.G T 2≤2*P+T.card ∧ 2*chosenSlots F.G T 3≤P := by
  intro P
  have first (c) (hc:c∈T) : 3*(Nat.card c.supp/3)≤2*matchingEdges c.toSimpleGraph+1 := by
    have order := (strict_six_true_component_capacity F paid six c (actual c hc)).2.1
    omega
  have second (c) (hc:c∈T) : 2*(Nat.card c.supp/4)≤matchingEdges c.toSimpleGraph := by
    have order := (strict_six_true_component_capacity F paid six c (actual c hc)).2.1
    omega
  have a := Finset.sum_le_sum (s:=T) (fun c hc => first c hc)
  have b := Finset.sum_le_sum (s:=T) (fun c hc => second c hc)
  rw [←Finset.mul_sum,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const] at a
  rw [←Finset.mul_sum] at b
  simp only [nsmul_eq_mul,Nat.cast_id,mul_one] at a
  have rank := (component_union_accounts F.G T).2.1
  change P=∑c∈T,matchingEdges c.toSimpleGraph at rank
  rw [←rank] at a b
  exact ⟨a,b⟩

theorem strict_two_or_three_capacity_total (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) (size:T.card=2 ∨ T.card=3)
    (width:highestWidth F.n F.m F.r≤T.card+1) :
    matchingEdges (F.G.induce (componentVertices F.G T))≤3*(F.rank-matchingEdges F.G) := by
  have price := (strict_six_chosen_edge_price F paid six T actual).1 width
  have slots := (strict_chosen_slot_totals F paid six T actual).1
  rcases size with two|three <;> omega

#print axioms strict_chosen_slot_totals
#print axioms strict_two_or_three_capacity_total
end JSP452Audit.StarHost
