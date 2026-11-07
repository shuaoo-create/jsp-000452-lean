import UpToThreeEightRegularComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_price_with_one_lower_column (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (j W:ℕ) (low:2≤j) (high:j≤7)
    (extra:widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+W) :
    let P := ∑c∈T,Nat.card c.supp/2
    let U := componentVertices F.G T
    let d := F.rank-matchingEdges F.G
    2*P+4*T.card+2+(P-matchingEdges (F.G.induce U))≤d+2*highestWidth F.n F.m F.r+
      chosenSlots F.G T 2+W+5*((T.card-1)/2) := by
  intro P U d
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T 2
  let e := (T.card-1)/2
  let tax (i:ℕ) := if i=8 then M+(h-1) else if i=j then W else P+e
  obtain ⟨reds,blues,_⟩ := strict_only_double_escape F paid
  have r (i) : F.n i+2≤9 := by have hi := reds i;rw [eight] at hi;omega
  have b (i) : F.m i+2≤9 := by have hi := blues i;rw [eight] at hi;omega
  have last := strict_eighth_column_slot_tax F paid eight T 2 r b
  have costs (i:ℕ) (lo:2 ≤ i) (_:i≤8) : widthAt F.n F.m F.r i≤uniformEnvelope (F.G.induce Uᶜ) i+tax i := by
    by_cases top:i=8
    · subst i;simpa [tax,U,M,h,Nat.add_assoc] using last
    by_cases one:i=j
    · subst i;simpa [tax,top,U] using extra
    simpa [tax,top,one,U,P,e] using eight_low_column_price_for_three F paid eight T actual i (by omega)
  have budget := eight_exterior_column_budget F paid eight T actual tax costs
  have sum : (∑q∈Finset.range 7,tax (q+2))=5*(P+e)+W+M+(h-1) := by
    dsimp only [tax]
    interval_cases j <;> simp [Finset.sum_range_succ] <;> omega
  change 8*P+4*T.card+1≤matchingEdges (F.G.induce U)+d+h+_ at budget
  rw [sum] at budget
  have rank := (regular_union_at_even_degree F.G 4 T actual).2.2.1
  change matchingEdges (F.G.induce U)≤P at rank
  have hp : 1≤h := (strict_eight_inventory F paid eight).1
  change _≤d+2*h+M+W+5*e
  omega

theorem eight_price_before_lower_improvement (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8) :
    let P := ∑c∈T,Nat.card c.supp/2
    let U := componentVertices F.G T
    let d := F.rank-matchingEdges F.G
    P+4*T.card+2+(P-matchingEdges (F.G.induce U))≤d+2*highestWidth F.n F.m F.r+chosenSlots F.G T 2+6*((T.card-1)/2) := by
  intro P U d
  have cost := eight_low_column_price_for_three F paid eight T actual 2 (by decide)
  have both := eight_price_with_one_lower_column F paid eight T actual 2 (P+(T.card-1)/2) (by decide) (by decide) cost
  change 2*P+4*T.card+2+(P-matchingEdges (F.G.induce U))≤d+2*highestWidth F.n F.m F.r+chosenSlots F.G T 2+
    (P+(T.card-1)/2)+5*((T.card-1)/2) at both
  omega

#print axioms eight_price_with_one_lower_column
#print axioms eight_price_before_lower_improvement
end JSP452Audit.StarHost
