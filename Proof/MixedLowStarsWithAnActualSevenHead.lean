import TwoColumnPricesForThreeComponents
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_regular_endpoint_sizes (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8) :
    let U := componentVertices F.G T
    let Q := matchingEdges (F.G.induce U)
    let d := F.rank-matchingEdges F.G
    Q+F.r+2*d≤min F.s F.t ∧
    ∀(V:Set ↥(Uᶜ:Set F.X)) (H:ℕ),0<H → (∀v,Nat.card (((F.G.induce Uᶜ).induce Vᶜ).neighborSet v)<H) →
      (0<originalThresholdCount F.n H ∨ 0<originalThresholdCount F.m H) → 2*d≤V.ncard := by
  intro U Q d
  have closed := component_vertices_closed F.G T
  have full (x) (hx:x∈U) := ((actual (F.G.connectedComponentMk x) hx).2 x rfl).trans eight.symm
  obtain ⟨red,blue,layers⟩ := strict_exterior_parity_and_stages F paid U closed full
  change Q+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t at red
  change Q+F.r+2*(d+∑j,(F.m j-1)/2)≤F.s at blue
  refine ⟨by omega,?_⟩
  intro V H pos low heads
  have witness := layers V (H-1) (fun v => by have small := low v;omega)
  rw [show H-1+1=H by omega] at witness
  rcases heads with a|b
  · have need := witness.1 a
    change F.t-F.r-Q-1+originalThresholdCount F.n H≤V.ncard at need;omega
  · have need := witness.2 b
    change F.s-F.r-Q-1+originalThresholdCount F.m H≤V.ncard at need;omega

theorem eight_mixed_winner_improves_cost (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent) (actual:∀c∈T,c∈oddRegularComponents F.G 8)
    (types:EightSelectionSize T.card (highestWidth F.n F.m F.r))
    (heads:0<originalThresholdCount F.n 7 ∨ 0<originalThresholdCount F.m 7)
    (j a b:ℕ) (lo:2 ≤ j) (hi:j≤7) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+chosenSlots F.G T 2 := by
  let U := componentVertices F.G T
  let Q := matchingEdges (F.G.induce U)
  let P := ∑c∈T,Nat.card c.supp/2
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T 2
  let L := widthAt F.n F.m F.r j
  have price := eight_price_before_lower_improvement F paid eight T actual
  change P+4*T.card+2+(P-Q)≤d+2*h+M+6*((T.card-1)/2) at price
  have ord := (regular_half_order_slot_counts F.G 8 T actual).1
  change 3*M≤2*P+T.card at ord
  have len := (eight_regular_endpoint_sizes F paid eight T actual).1
  change Q+F.r+2*d≤min F.s F.t at len
  have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht (by omega : 0<j) hi
  change min F.s F.t-F.r≤L at floor
  have dpos := (minimal_strict_source_deficit F paid).2.1
  rw [eight] at dpos
  have hp := (strict_eight_inventory F paid eight).2.1
  change h≤minimumExposure F.G 8 at hp
  have rank := (regular_union_at_even_degree F.G 4 T actual).2.2.1
  change Q≤P at rank
  obtain ⟨ap,bp,height,red,blue,width⟩ := win
  change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at width
  change EightSelectionSize T.card h at types
  have large : M<originalThresholdCount F.n a ∨ M<originalThresholdCount F.m b := by
    change minimumExposure F.G 8+1≤d at dpos
    unfold EightSelectionSize at types;rcases types with c|c|c <;> omega
  have row := closed_union_sum_row F.G U (component_vertices_closed F.G T) F.row
  rcases large with aa|bb
  · have fee := mono_red_rectangle _ _ F.n F.m F.hn F.hm ap bp
      (pack_cap_for_larger_heads _ ra (selected_component_pack F.G T 2 (by decide))) aa blue row
    rwa [←width,height] at fee
  · have fee := mono_blue_rectangle _ _ F.n F.m F.hn F.hm ap bp red
      (pack_cap_for_larger_heads _ bl (selected_component_pack F.G T 2 (by decide))) bb row
    rwa [←width,height] at fee

#print axioms eight_regular_endpoint_sizes
#print axioms eight_mixed_winner_improves_cost
end JSP452Audit.StarHost
