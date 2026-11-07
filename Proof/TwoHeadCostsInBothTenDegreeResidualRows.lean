import ALargeMixedTenthColumnForcesTheJoinedResidualToUnits
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_positive_blue_threshold_cost (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s)
    (j : ℕ) (active : 0<originalThresholdCount F.m j) :
    let W := componentBudget (F.G.induce R.core) F.n
    let delta := R.capacity-W.loss
    2*(F.s+delta+originalThresholdCount F.m j)≤R.basicPrice F.n F.m F.r j+2*(F.r+1) := by
  intro W delta
  let P := R.capacity
  let a := R.roots.ncard
  let J := commonErasedDemand F.n W a P
  have fee := ten_long_side_two_prices F paid ten R small many long
  have fit : W.loss≤P := fee.2.2.1
  have live : 0<W.len := fee.1
  have left := original_threshold_one (W.entries F.n) (W.entries_positive F.n F.pn)
  have right := original_threshold_one J (common_erased_positive F.n W a P)
  have b := actual_rectangle_le_column (r:=F.r+a) (W.entries F.n) F.m (W.entries_antitone F.n F.hn) F.hm
    (a:=1) (b:=j) (h:=j) (by omega) (left.symm ▸ live) active
  have z := actual_rectangle_le_column (r:=F.r) J F.m (common_erased_antitone F.n F.hn W a P) F.hm
    (a:=1) (b:=j) (h:=j) (by omega) (right.symm ▸ live) active
  rw [left] at b;rw [right] at z
  have size : W.len+P=F.s+delta := by change (F.s-W.loss)+P=F.s+(P-W.loss);change P<F.s at long;omega
  change 2*(F.s+delta+originalThresholdCount F.m j)≤a+2*P+widthAt (W.entries F.n) F.m (F.r+a) j+
    widthAt J F.m F.r j+2*(F.r+1)
  omega

theorem ten_two_head_basic_cost (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s)
    (j y : ℕ) (active : 0<originalThresholdCount F.m j) (win : WinsHeight F.n F.m F.r j 2 y)
    (present : 0<widthAt F.n F.m F.r j) :
    let W := componentBudget (F.G.induce R.core) F.n
    let delta := R.capacity-W.loss
    let u := F.s-originalThresholdCount F.n 2
    2*widthAt F.n F.m F.r j+2*(u+delta+originalThresholdCount F.m j)≤
      R.basicPrice F.n F.m F.r j+2*originalThresholdCount F.m y := by
  intro W delta u
  have fee := ten_positive_blue_threshold_cost F paid ten R small many long j active
  change 2*(F.s+delta+originalThresholdCount F.m j)≤R.basicPrice F.n F.m F.r j+2*(F.r+1) at fee
  have size := original_threshold_le_length F.n 2
  have width := win.2.2.2.2.2
  dsimp only [u];omega

theorem ten_two_head_inventory_cost (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s)
    (j y : ℕ) (pos : 0<j) (active : 0<originalThresholdCount F.m j) (win : WinsHeight F.n F.m F.r j 2 y)
    (present : 0<widthAt F.n F.m F.r j) :
    let W := componentBudget (F.G.induce R.core) F.n
    let delta := R.capacity-W.loss
    let u := F.s-originalThresholdCount F.n 2
    2*widthAt F.n F.m F.r j+2*(u+delta+originalThresholdCount F.m j)≤
      R.jointPrice j+2*originalThresholdCount F.m y := by
  intro W delta u
  have fee := ten_two_head_basic_cost F paid ten R small many long j y active win present
  have le := ten_actual_columns_below_inventory F paid ten R small many long j pos
  change 2*widthAt F.n F.m F.r j+2*(u+delta+originalThresholdCount F.m j)≤_ at fee
  omega

#print axioms ten_positive_blue_threshold_cost
#print axioms ten_two_head_basic_cost
#print axioms ten_two_head_inventory_cost
end JSP452Audit.StarHost
