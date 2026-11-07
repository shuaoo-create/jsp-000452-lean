import EveryLowColumnOfTheTwoLongLists
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_live_mixed_column (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<min F.s F.t)
    (j a b H : ℕ) (lo : 2≤j) (hi : j≤H)
    (head : 0<originalThresholdCount F.n H ∨ 0<originalThresholdCount F.m H)
    (wa : 2≤a) (wb : 2≤b) (win : WinsHeight F.n F.m F.r j a b) :
    widthAt F.n F.m F.r j≤uniformEnvelope R.erased j+R.slotDamage 2 := by
  let P := R.totalCapacity
  let M := R.slotDamage 2
  let d := F.rank-matchingEdges F.G
  let L := widthAt F.n F.m F.r j
  obtain ⟨rn,bm,_⟩ := strict_only_double_escape F paid
  have red (i) : F.n i+2≤10 := by have lim := rn i;rw [nine] at lim;omega
  have blue (i) : F.m i+2≤10 := by have lim := bm i;rw [nine] at lim;omega
  have reserve := strict_nine_two_long_deficit F paid nine R long 2 red blue
  have h := (strict_nine_original_peak F paid nine).2.1
  change P+9+R.portCount+envelopeReserve R.erased 8≤d+2*highestWidth F.n F.m F.r+M at reserve
  have slot := R.port_slot_sizes.1
  change 3*M≤2*P+4+R.portCount at slot
  have window := strict_nine_capacity_window F paid nine R
  have sLong := window.2.1 (lt_min_iff.mp long).1
  have tLong := window.2.2.2.1 (lt_min_iff.mp long).2
  change P+F.r+2*(d+_)≤F.s at sLong
  change P+F.r+2*(d+_)≤F.t at tLong
  have base := lower_axis_at_any_head (r:=F.r) F.n F.m F.hn F.hm F.pn F.pm head F.hs F.ht (by omega : 0<j) hi
  change min F.s F.t-F.r≤L at base
  have aTax : R.starTax a≤M := (Nat.min_le_right _ _).trans (R.port_slot_decreases wa)
  have bTax : R.starTax b≤M := (Nat.min_le_right _ _).trans (R.port_slot_decreases wb)
  obtain ⟨pa,pb,hgt,ar,br,width⟩ := win
  have cases := R.original_port_winner_alternatives F.n F.m F.hn F.hm ⟨pa,pb,hgt,ar,br,width⟩ F.row
  change L=originalThresholdCount F.n a+originalThresholdCount F.m b-1-F.r at width
  change L≤uniformEnvelope R.erased j+M
  rcases cases with left|right|⟨deadA,deadB⟩
  · change L≤uniformEnvelope R.erased j+R.starTax a at left;omega
  · change L≤uniformEnvelope R.erased j+R.starTax b at right;omega
  · omega

theorem nine_seven_head_stage_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (red : ∀i,F.n i≤7) (blue : ∀j,F.m j≤7)
    (H : ThreeDegreeStages R.erased 7) :
    portMenuGap R.capacity-(F.r+1)≤H.lastCut.ncard := by
  let P := R.totalCapacity
  let d := F.rank-matchingEdges F.G
  let M := R.slotDamage 3
  have reserve := strict_nine_two_long_deficit F paid nine R long 3 (fun i => by have := red i;omega)
    (fun j => by have := blue j;omega)
  change P+9+R.portCount+envelopeReserve R.erased 8≤d+2*highestWidth F.n F.m F.r+M at reserve
  have slot := R.port_slot_sizes.2.1
  change 4*M≤2*P+4+2*R.portCount at slot
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have inventory := (strict_nine_actual_stage_inventory F paid nine R H).2.2.1 long
  change 2*d+6≤H.lastCut.ncard at inventory
  have gap : portMenuGap R.capacity≤P := by
    change max (min _ _) (max _ _-min _ _)≤R.capacity 0+R.capacity 1
    omega
  omega

#print axioms strict_nine_live_mixed_column
#print axioms nine_seven_head_stage_inventory
end JSP452Audit.StarHost
