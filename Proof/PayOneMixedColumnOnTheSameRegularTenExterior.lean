import TheSingleAndPairedRegularMenusAtDegreeTen
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_closed_endpoint_sizes (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) :
    let U := K.support
    let Q := matchingEdges (F.G.induce U)
    let d := F.rank-matchingEdges F.G
    Q+F.r+2*d≤min F.s F.t ∧
    ∀(V:Set ↥(Uᶜ:Set F.X)) (H:ℕ),0<H → (∀v,Nat.card (((F.G.induce Uᶜ).induce Vᶜ).neighborSet v)<H) →
      (0<originalThresholdCount F.n H ∨ 0<originalThresholdCount F.m H) → 2*d≤V.ncard := by
  intro U Q d
  have closed := K.support_closed
  have full (x) (hx:x∈U) := (K.support_full x hx).trans ten.symm
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



theorem ten_mixed_column_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G)
    (cost:6*highestWidth F.n F.m F.r≤13*K.eps+6)
    (heads:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9)
    (j a b:ℕ) (lo:2≤j) (hi:j≤9) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce K.supportᶜ) j+chosenSlots F.G K.selected 2 := by
  let P := K.P
  let Q := matchingEdges (F.G.induce K.support)
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G K.selected 2
  let L := widthAt F.n F.m F.r j
  have price := ten_regular_unconditional_volume F paid ten K
  change P+14*K.eps+6+3*(P-Q)≤3*d+6*h at price
  have ord := ten_regular_slot_volume K 2
  change 3*M≤2*P+K.eps at ord
  have len := (ten_closed_endpoint_sizes F paid ten K).1
  change Q+F.r+2*d≤min F.s F.t at len
  have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm heads F.hs F.ht (by omega : 0<j) hi
  change min F.s F.t-F.r≤L at floor
  obtain ⟨ap,bp,height,red,blue,width⟩ := win
  change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at width
  change 6*h≤13*K.eps+6 at cost
  have fit : Q≤P := K.fits
  have sm := K.small
  have positive := (minimal_strict_source_deficit F paid).2.2
  change 2≤d at positive
  have large : M<originalThresholdCount F.n a ∨ M<originalThresholdCount F.m b := by omega
  have row := closed_union_sum_row F.G K.support K.support_closed F.row
  rcases large with aa|bb
  · have fee := mono_red_rectangle _ _ F.n F.m F.hn F.hm ap bp
      (pack_cap_for_larger_heads _ ra (selected_component_pack F.G K.selected 2 (by decide))) aa blue row
    rwa [←width,height] at fee
  · have fee := mono_blue_rectangle _ _ F.n F.m F.hn F.hm ap bp red
      (pack_cap_for_larger_heads _ bl (selected_component_pack F.G K.selected 2 (by decide))) bb row
    rwa [←width,height] at fee

#print axioms ten_closed_endpoint_sizes
#print axioms ten_mixed_column_price
end JSP452Audit.StarHost
