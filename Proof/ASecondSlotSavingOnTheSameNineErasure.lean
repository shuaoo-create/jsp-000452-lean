import AMixedLowWinnerPaysTheSmallerSlotTax
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_two_slot_savings (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (j a b : ℕ) (lo : 2≤j) (hi : j≤8)
    (heads : 0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8)
    (wa : 2≤a) (wb : 2≤b) (win : WinsHeight F.n F.m F.r j a b) :
    let P := R.totalCapacity
    let M := R.slotDamage 2
    let d := F.rank-matchingEdges F.G
    2*P+9+R.portCount+envelopeReserve R.erased 8≤d+2*highestWidth F.n F.m F.r+2*M := by
  classical
  intro P M d
  let h := highestWidth F.n F.m F.r
  let old (v : ℕ) := if v=9 then M+(h-1) else P+(if v=3 then 1 else 0)
  let tax (v : ℕ) := if v=j then M else old v
  obtain ⟨red,blue,_⟩ := strict_only_double_escape F paid
  have rn (i) : F.n i+2≤10 := by have lim := red i;rw [nine] at lim;omega
  have bm (i) : F.m i+2≤10 := by have lim := blue i;rw [nine] at lim;omega
  have near := (strict_nine_ninth_column_restoration F paid nine R 2 rn bm).1
  have low := strict_nine_live_mixed_column F paid nine R long j a b 8 lo hi heads wa wb win
  have fees (v) (lower : 2≤v) (upper : v≤9) : widthAt F.n F.m F.r v≤uniformEnvelope R.erased v+tax v := by
    by_cases eq : v=j
    · subst v;simpa [tax,M] using low
    · by_cases last : v=9
      · subst v;simpa [tax,eq,old,M,h,Nat.add_assoc] using near
      · simpa [tax,eq,old,last,P,Nat.add_assoc] using strict_nine_two_long_low_columns F R long v lower
  let S := Finset.range 8
  let x := j-2
  have mem : x∈S := Finset.mem_range.mpr (by dsimp [x];omega)
  have atJ : x+2=j := by dsimp [x];omega
  have total : (∑i∈S,old (i+2))=7*P+1+M+(h-1) := by simp [S,Finset.sum_range_succ,old];omega
  have equal : (∑i∈S.erase x,tax (i+2))=∑i∈S.erase x,old (i+2) := by
    apply Finset.sum_congr rfl
    intro i inside
    have ne := (Finset.mem_erase.mp inside).1
    rw [show tax (i+2)=old (i+2) from if_neg (by omega : ¬i+2=j)]
  have oldSum := Finset.sum_erase_add (s:=S) (f:=fun i => old (i+2)) mem
  have newSum := Finset.sum_erase_add (s:=S) (f:=fun i => tax (i+2)) mem
  rw [atJ,show tax j=M from if_pos rfl,equal] at newSum
  rw [atJ,total] at oldSum
  have oldFee : P≤old j := by dsimp only [old];rw [if_neg (by omega : j≠9)];omega
  have price := strict_nine_port_column_account F paid nine R tax fees
  change 8*P+9+R.portCount+envelopeReserve R.erased 8≤d+h+(∑i∈S,tax (i+2)) at price
  change 2*P+9+R.portCount+envelopeReserve R.erased 8≤d+2*h+2*M
  have hp : 1≤h := (strict_nine_original_peak F paid nine).1
  omega

theorem nine_eight_head_mixed_stage_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (j a b : ℕ) (lo : 2≤j) (hi : j≤8)
    (heads : 0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8)
    (wa : 2≤a) (wb : 2≤b) (win : WinsHeight F.n F.m F.r j a b) (H : ThreeDegreeStages R.erased 7) :
    portMenuGap R.capacity-(F.r+1)≤H.midCut.ncard := by
  let P := R.totalCapacity
  let M := R.slotDamage 2
  let d := F.rank-matchingEdges F.G
  have pay := nine_two_slot_savings F paid nine R long j a b lo hi heads wa wb win
  change 2*P+9+R.portCount+envelopeReserve R.erased 8≤d+2*highestWidth F.n F.m F.r+2*M at pay
  have slot := R.port_slot_sizes.1
  change 3*M≤2*P+4+R.portCount at slot
  have count := R.physical_tip_and_root_counts.2.2
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have cap := (H.degree_caps (nine_erased_degree_cap F paid nine R)).2.1
  have stage := strict_nine_live_head_requires_vertices F paid R 7 H.midCut cap
  have supply : 2*d≤H.midCut.ncard := by
    rcases heads with red|blue
    · have budget := stage.1 (lt_min_iff.mp long).2 red
      change 2*(d+_)+originalThresholdCount F.n 8≤H.midCut.ncard+1 at budget;omega
    · have budget := stage.2 (lt_min_iff.mp long).1 blue
      change 2*(d+_)+originalThresholdCount F.m 8≤H.midCut.ncard+1 at budget;omega
  have gap : portMenuGap R.capacity≤P := by
    change max (min _ _) (max _ _-min _ _)≤R.capacity 0+R.capacity 1
    omega
  omega

#print axioms nine_two_slot_savings
#print axioms nine_eight_head_mixed_stage_inventory
end JSP452Audit.StarHost
