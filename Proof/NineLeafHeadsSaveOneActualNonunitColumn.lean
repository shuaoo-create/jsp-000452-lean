import ActualHighDegreeDeletionCountsOnThePortExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_port_nine_head_mixed_savings (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) {K:TenBlockPartition F.G}
    (W:TenPortSupport F.G K (highestWidth F.n F.m F.r))
    (narrow:highestWidth F.n F.m F.r≤2) (deep:highestWidth F.n F.m F.r+3≤F.rank-matchingEdges F.G)
    (length:W.rank+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t)
    (head:0<originalThresholdCount F.n 9 ∨ 0<originalThresholdCount F.m 9)
    (j a b:ℕ) (lo:2≤j) (hi:j≤9) (na:2≤a) (mb:2≤b) (win:WinsHeight F.n F.m F.r j a b) :
    widthAt F.n F.m F.r j≤uniformEnvelope W.outside j+W.slotDamage 2 := by
  let d := F.rank-W.rank-matchingEdges W.outside
  let h := highestWidth F.n F.m F.r
  let P := W.half
  let M := W.slotDamage 2
  have pos := (strict_ten_inventory F paid ten).1
  have volume := (ten_port_volume_two_three F paid ten W deep length).1
  change P+3*(P-W.rank)+14*W.parity+W.portCount+3≤3*d+6*h at volume
  have book := W.size_and_fee pos
  have positive : W.parity=1 ∨ W.parity=2 := book.2.2.1
  have fees := (W.port_slot_sizes pos).1
  change 3*M≤2*P+W.parity+2*W.portCount at fees
  have len := (ten_port_exterior_stock F W deep length).1
  change W.rank+F.r+2*d≤min F.s F.t at len
  have floor := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm head F.hs F.ht (by omega : 0<j) hi
  obtain ⟨pa,pb,eq,red,blue,width⟩ := win
  have taxA : W.starTax a≤M := (Nat.min_le_right _ _).trans (W.port_slot_decreases na)
  have taxB : W.starTax b≤M := (Nat.min_le_right _ _).trans (W.port_slot_decreases mb)
  have fee := W.actual_exterior_rectangles F.n F.m F.hn F.hm ⟨pa,pb,eq,red,blue,width⟩ F.row
  change h≤2 at narrow
  change min F.s F.t-F.r≤widthAt F.n F.m F.r j at floor
  have fit : W.rank≤P := book.2.2.2.2.1
  have small : W.portCount≤2 := book.2.1
  omega

#print axioms ten_port_nine_head_mixed_savings
end JSP452Audit.StarHost
