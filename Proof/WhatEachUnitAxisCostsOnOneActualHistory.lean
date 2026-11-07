import NineDegreeTwoLongSourcesMustPassTheEightStage
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_erased_unit_axis_counts (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : NinePortRegion F.G) (long : R.totalCapacity<min F.s F.t)
    (T : ℕ→Set F.X) (history : DegreeCutAccount R.erased 9 T) :
    F.rank≤R.totalCapacity+(T 1).ncard ∧
      ∀j,0<j → j≤9 →
      (0<originalThresholdCount F.n j →
        originalThresholdCount F.n j+F.t-1-F.r≤R.totalCapacity+(T j).ncard) ∧
      (0<originalThresholdCount F.m j →
        F.s+originalThresholdCount F.m j-1-F.r≤R.totalCapacity+(T j).ncard) := by
  let P := R.totalCapacity
  let d := F.rank-matchingEdges F.G
  let q := F.t-F.r-P
  let k := F.s-F.r-P
  have orig := strict_nine_actual_erased_endpoints F paid R
  obtain ⟨posR,_,sumR,epR,_⟩ := orig.1 (lt_min_iff.mp long).2
  obtain ⟨posB,_,sumB,epB,_⟩ := orig.2 (lt_min_iff.mp long).1
  change d+1≤q at posR;change d+1≤k at posB
  change matchingEdges R.erased+d+1=F.s+q at sumR
  have bounds (j) (pos : 0<j) (le : j≤9) :
      (0<originalThresholdCount F.n j → q-1+originalThresholdCount F.n j≤(T j).ncard) ∧
      (0<originalThresholdCount F.m j → k-1+originalThresholdCount F.m j≤(T j).ncard) := by
    have cap (v) : Nat.card ((R.erased.induce (T j)ᶜ).neighborSet v)≤j-1 := by
      have lim := history.1 j pos le v;omega
    constructor
    · intro head;simpa only [Nat.sub_add_cancel pos] using endpoint_threshold_stage R.erased F.n F.pn epR (by omega) (T j) cap (by rwa [Nat.sub_add_cancel pos])
    · intro head;simpa only [Nat.sub_add_cancel pos] using endpoint_threshold_stage R.erased F.m F.pm epB (by omega) (T j) cap (by rwa [Nat.sub_add_cancel pos])
  have one := (bounds 1 (by decide) (by decide)).1
  rw [original_threshold_one F.n F.pn] at one
  have top := one F.hs
  have er := R.exact_port_partition.2.1
  have beneath := (minimal_rank_exact_source F paid).2.2.1
  have total : F.rank=P+matchingEdges R.erased+d := by
    change matchingEdges R.erased+P=matchingEdges F.G at er;dsimp only [d];omega
  refine ⟨by change F.rank≤P+_;omega,?_⟩
  intro j pos le
  obtain ⟨red,blue⟩ := bounds j pos le
  constructor
  · intro head;have h := red head
    dsimp only [q] at h posR
    change originalThresholdCount F.n j+F.t-1-F.r≤P+_;omega
  · intro head;have h := blue head
    dsimp only [k] at h posB
    change F.s+originalThresholdCount F.m j-1-F.r≤P+_;omega

theorem nine_unit_winner_on_history (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (R : NinePortRegion F.G) (long : R.totalCapacity<min F.s F.t)
    (T : ℕ→Set F.X) (history : DegreeCutAccount R.erased 9 T)
    (j a b : ℕ) (pos : 0<j) (le : j≤9) (win : WinsHeight F.n F.m F.r j a b)
    (axis : a=1 ∨ b=1) : widthAt F.n F.m F.r j≤R.totalCapacity+(T j).ncard := by
  have fees := (nine_erased_unit_axis_counts F paid R long T history).2 j pos le
  obtain ⟨pa,pb,hgt,red,blue,width⟩ := win
  rcases axis with rfl|rfl
  · have same : b=j := by omega
    subst b
    rw [original_threshold_one F.n F.pn] at width
    exact width ▸ fees.2 blue
  · have same : a=j := by omega
    subst a
    rw [original_threshold_one F.m F.pm] at width
    exact width ▸ fees.1 red

#print axioms nine_erased_unit_axis_counts
#print axioms nine_unit_winner_on_history
end JSP452Audit.StarHost
