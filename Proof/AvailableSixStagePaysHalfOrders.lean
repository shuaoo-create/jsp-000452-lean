import ExcludeSevenLeafHeadsAtDegreeEight
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_deficit_after_seven_head_exclusion (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8) :
    let P := ∑c∈T,Nat.card c.supp/2
    let U := componentVertices F.G T
    let d := F.rank-matchingEdges F.G
    P+4*T.card+2+(P-matchingEdges (F.G.induce U))≤d+2*highestWidth F.n F.m F.r+
      chosenSlots F.G T 3+6*((T.card-1)/2) := by
  intro P U d
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T 3
  let e := (T.card-1)/2
  let tax (i:ℕ) := if i=8 then M+(h-1) else P+e
  obtain ⟨red,blue⟩ := strict_eight_no_seven_head F paid eight
  have last := strict_eighth_column_slot_tax F paid eight T 3 (fun i => by have := red i;omega) (fun j => by have := blue j;omega)
  have costs (i:ℕ) (lo:2 ≤ i) (_:i≤8) : widthAt F.n F.m F.r i≤uniformEnvelope (F.G.induce Uᶜ) i+tax i := by
    by_cases top:i=8
    · subst i;simpa [tax,U,M,h,Nat.add_assoc] using last
    simpa [tax,top,U,P,e] using eight_low_column_price_for_three F paid eight T actual i (by omega)
  have budget := eight_exterior_column_budget F paid eight T actual tax costs
  have sum : (∑q∈Finset.range 7,tax (q+2))=6*(P+e)+M+(h-1) := by simp [Finset.sum_range_succ,tax];omega
  change 8*P+4*T.card+1≤matchingEdges (F.G.induce U)+d+h+_ at budget
  rw [sum] at budget
  have rank := (regular_union_at_even_degree F.G 4 T actual).2.2.1
  change matchingEdges (F.G.induce U)≤P at rank
  have hp : 1≤h := (strict_eight_inventory F paid eight).1
  change _≤d+2*h+M+6*e
  omega

theorem selected_eight_half_orders_fit_six_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (types:EightSelectionSize T.card (highestWidth F.n F.m F.r)) :
    ∀c∈T,Nat.card c.supp/2≤2*(F.rank-matchingEdges F.G) := by
  let P := ∑q∈T,Nat.card q.supp/2
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T 3
  let d := F.rank-matchingEdges F.G
  have fee := eight_deficit_after_seven_head_exclusion F paid eight T actual
  change P+4*T.card+2+(P-matchingEdges (F.G.induce (componentVertices F.G T)))≤d+2*h+M+6*((T.card-1)/2) at fee
  have slots := (regular_half_order_slot_counts F.G 8 T actual).2
  change 2*M≤P at slots
  intro c mem
  have others := selected_half_and_other_minima F.G T actual c mem
  change Nat.card c.supp/2+4*(T.card-1)≤P at others
  change Nat.card c.supp/2≤2*d
  change EightSelectionSize T.card h at types
  unfold EightSelectionSize at types;rcases types with v|v|v <;> omega

#print axioms eight_deficit_after_seven_head_exclusion
#print axioms selected_eight_half_orders_fit_six_stage
end JSP452Audit.StarHost
