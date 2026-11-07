import MixedLowStarsWithAnActualSevenHead
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem selected_half_and_other_minima {X:Type*} [Finite X] (G:SimpleGraph X)
    (T:Finset G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents G 8)
    (c:G.ConnectedComponent) (mem:c∈T) :
    Nat.card c.supp/2+4*(T.card-1)≤∑q∈T,Nat.card q.supp/2 := by
  classical
  have each (q:G.ConnectedComponent) (hq:q∈T.erase c) : 4≤Nat.card q.supp/2 := by
    let v := q.nonempty_supp.to_subtype.some
    have reg := (component_degree_eq G q v).trans ((actual q (Finset.mem_of_mem_erase hq)).2 v.val v.property)
    exact half_order_of_regular_component q.toSimpleGraph 4 v reg
  have many := Finset.sum_le_sum (s:=T.erase c) each
  rw [Finset.sum_const,Finset.card_erase_of_mem mem,nsmul_eq_mul,Nat.cast_id] at many
  have sum := Finset.add_sum_erase T (fun q:G.ConnectedComponent => Nat.card q.supp/2) mem
  omega

theorem mixed_eight_winner_caps_every_selected_order (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8)
    (types:EightSelectionSize T.card (highestWidth F.n F.m F.r))
    (heads:0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7)
    (j a b:ℕ) (lo:2 ≤ j) (hi:j≤7) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    ∀c∈T,Nat.card c.supp/2≤2*(F.rank-matchingEdges F.G) := by
  let U := componentVertices F.G T
  let P := ∑c∈T,Nat.card c.supp/2
  let Q := matchingEdges (F.G.induce U)
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T 2
  have enhanced := eight_mixed_winner_improves_cost F paid eight T actual types heads j a b lo hi ra bl win
  have budget := eight_price_with_one_lower_column F paid eight T actual j M lo hi enhanced
  change 2*P+4*T.card+2+(P-Q)≤d+2*h+M+M+5*((T.card-1)/2) at budget
  have slots := (regular_half_order_slot_counts F.G 8 T actual).1
  change 3*M≤2*P+T.card at slots
  intro c mem
  have all := selected_half_and_other_minima F.G T actual c mem
  change Nat.card c.supp/2+4*(T.card-1)≤P at all
  change Nat.card c.supp/2≤2*d
  change EightSelectionSize T.card h at types
  unfold EightSelectionSize at types;rcases types with m|m|m <;> omega

#print axioms selected_half_and_other_minima
#print axioms mixed_eight_winner_caps_every_selected_order
end JSP452Audit.StarHost
