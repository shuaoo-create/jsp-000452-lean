import PayOneMixedColumnOnTheSameRegularTenExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_closed_price_with_extra_column (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (j W:ℕ) (lo:2≤j) (hi:j≤9)
    (extra:widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce K.supportᶜ) j+W) :
    2*K.P+5*K.eps+2+K.slack≤(F.rank-matchingEdges F.G)+2*highestWidth F.n F.m F.r+chosenSlots F.G K.selected 2+W := by
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G K.selected 2
  let tax (i:ℕ) := if i=10 then M+(h-1) else if i=j then W else K.P
  obtain ⟨reds,blues,_⟩ := strict_only_double_escape F paid
  have red (i) : F.n i+2≤11 := by have bounds := reds i;rw [ten] at bounds;omega
  have blue (i) : F.m i+2≤11 := by have bounds := blues i;rw [ten] at bounds;omega
  have last := strict_tenth_column_slot_tax F paid ten K.selected 2 red blue
  change widthAt F.n F.m F.r 10≤uniformEnvelope (F.G.induce K.supportᶜ) 10+M+(h-1) at last
  have cols (i : ℕ) (low : 2 ≤ i) (_:i≤10) : widthAt F.n F.m F.r i≤uniformEnvelope (F.G.induce K.supportᶜ) i+tax i := by
    by_cases top:i=10
    · subst i;simpa only [tax,if_pos rfl,Nat.add_assoc] using last
    by_cases same:i=j
    · subst i;simpa [tax,top] using extra
    · simpa only [tax,if_neg top,if_neg same] using ten_closed_low_column_tax F paid ten K i (by omega)
  have bill := ten_closed_exterior_column_budget F paid ten K tax cols
  have sum : (∑q∈Finset.range 9,tax (q+2))=7*K.P+W+M+(h-1) := by
    dsimp only [tax];interval_cases j <;> simp [Finset.sum_range_succ] <;> omega
  change 10*K.P+5*K.eps+1≤matchingEdges (F.G.induce K.support)+(F.rank-matchingEdges F.G)+h+_ at bill
  rw [sum] at bill
  have fit : matchingEdges (F.G.induce K.support)≤K.P := K.fits
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  change 2*K.P+5*K.eps+2+(K.P-matchingEdges (F.G.induce K.support))≤_+2*h+M+W
  omega

theorem ten_nine_leaf_mixed_capacity (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G)
    (cost:6*highestWidth F.n F.m F.r≤13*K.eps+6)
    (heads:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9)
    (j a b:ℕ) (lo:2≤j) (hi:j≤9) (ra:2≤a) (bl:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    K.P≤2*(F.rank-matchingEdges F.G) := by
  let M := chosenSlots F.G K.selected 2
  have fee := ten_mixed_column_price F paid ten K cost heads j a b lo hi ra bl win
  have budget := ten_closed_price_with_extra_column F paid ten K j M lo hi fee
  have size := ten_regular_slot_volume K 2
  change 3*M≤2*K.P+K.eps at size
  change 2*K.P+5*K.eps+2+K.slack≤_+2*highestWidth F.n F.m F.r+M+M at budget
  omega
#print axioms ten_closed_price_with_extra_column
#print axioms ten_nine_leaf_mixed_capacity
end JSP452Audit.StarHost
