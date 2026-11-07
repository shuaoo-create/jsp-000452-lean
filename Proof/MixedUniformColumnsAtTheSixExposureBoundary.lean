import FourRealRegularComponentsAndOneConservativeUnit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
theorem ten_width_six_mixed_slot_price (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G)
    (six:highestWidth F.n F.m F.r=6) (eps:K.eps=2)
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
  change h=6 at six
  have fit : Q≤P := K.fits
  have sm := K.small
  have positive := (minimal_strict_source_deficit F paid).2.2
  change 2≤d at positive
  have wide := (strict_ten_inventory F paid ten).2.1
  have deep := (minimal_strict_source_deficit F paid).2.1
  rw [ten] at deep
  change minimumExposure F.G 10+1≤d at deep
  change h≤minimumExposure F.G 10 at wide
  have large : M<originalThresholdCount F.n a ∨ M<originalThresholdCount F.m b := by omega
  have row := closed_union_sum_row F.G K.support K.support_closed F.row
  rcases large with aa|bb
  · have fee := mono_red_rectangle _ _ F.n F.m F.hn F.hm ap bp
      (pack_cap_for_larger_heads _ ra (selected_component_pack F.G K.selected 2 (by decide))) aa blue row
    rwa [←width,height] at fee
  · have fee := mono_blue_rectangle _ _ F.n F.m F.hn F.hm ap bp red
      (pack_cap_for_larger_heads _ bl (selected_component_pack F.G K.selected 2 (by decide))) bb row
    rwa [←width,height] at fee


theorem ten_width_six_mixed_capacity (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (six:highestWidth F.n F.m F.r=6) (eps:K.eps=2)
    (head:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9) (j a b:ℕ)
    (lo:2≤j) (hi:j≤9) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    K.P≤2*(F.rank-matchingEdges F.G) := by
  have price := ten_width_six_mixed_slot_price F paid ten K six eps head j a b lo hi ra bl win
  have budget := ten_closed_price_with_extra_column F paid ten K j _ lo hi price
  have volume := ten_regular_slot_volume K 2
  have lower := (strict_ten_inventory F paid ten).2.1
  have gap := (minimal_strict_source_deficit F paid).2.1
  rw [ten] at gap
  omega

#print axioms ten_width_six_mixed_slot_price
#print axioms ten_width_six_mixed_capacity
end JSP452Audit.StarHost
