import AreaOfTheTwoActualTenDegreeResidualRows
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_actual_columns_below_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2) (many:1≤R.eta) (long : R.capacity<F.s)
    (j : ℕ) (positive : 0<j) : R.basicPrice F.n F.m F.r j≤R.jointPrice j := by
  let W := componentBudget (F.G.induce R.core) F.n
  let J := commonErasedDemand F.n W R.roots.ncard R.capacity
  have live : 0<W.len := (ten_long_side_two_prices F paid ten R small many long).1
  have rows := (ten_same_budget_on_two_graphs F paid R).1
  have first := widthAt_le_uniformEnvelope live F.ht (W.entries F.n) F.m (W.entries_antitone F.n F.hn) F.hm
    (W.entries_positive F.n F.pn) F.pm _ _ j rows.1 positive
  have last := widthAt_le_uniformEnvelope live F.ht J F.m
    (common_erased_antitone F.n F.hn W R.roots.ncard R.capacity) F.hm
    (common_erased_positive F.n W R.roots.ncard R.capacity) F.pm _ _ j rows.2 positive
  change widthAt (W.entries F.n) F.m (F.r+R.roots.ncard) j≤uniformEnvelope (F.G.induce R.rest) j at first
  change widthAt J F.m F.r j≤uniformEnvelope R.retainedEdges j at last
  change R.roots.ncard+2*R.capacity+widthAt (W.entries F.n) F.m (F.r+R.roots.ncard) j+
    widthAt J F.m F.r j≤R.roots.ncard+2*R.capacity+uniformEnvelope (F.G.induce R.rest) j+uniformEnvelope R.retainedEdges j
  omega

theorem ten_actual_missing_threshold (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) (small:R.epsilon≤2)
    (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta) (long : R.capacity<F.s) :
    ∃j,2≤j ∧ j≤10 ∧ R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j ∧
      (∃x y,WinsHeight F.n F.m F.r j x y) ∧
      ∀x y,WinsHeight F.n F.m F.r j x y →
        2≤x ∧ originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.core) F.n)
          R.roots.ncard R.capacity) x=0 ∧
        originalThresholdCount F.n x≤R.capacity ∧
        originalThresholdCount ((componentBudget (F.G.induce R.core) F.n).entries F.n) x≤R.roots.ncard := by
  have many : 1≤R.eta := by omega
  have area := ten_joint_residual_area F paid ten R small many long
  let W := componentBudget (F.G.induce R.core) F.n
  have find : ∃j,2≤j ∧ j≤10 ∧ R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by
    by_contra! no
    have sum := Finset.sum_le_sum (s:=Finset.range 9) (fun i mem => no (i+2) (by omega)
      (by have := Finset.mem_range.mp mem;omega))
    rw [←Finset.mul_sum] at sum
    change 2*interiorArea F.n F.m F.r 10≤_ at sum
    omega
  obtain ⟨j,lo,hi,unpaid⟩ := find
  have live := (ten_long_side_two_prices F paid ten R small many long).1
  have fit := (ten_long_side_two_prices F paid ten R small many long).2.2.1
  have lost := missing_threshold_of_two_budget_columns F.n F.m F.hn F.hm F.pn W fit live unpaid
  have present : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,pa,pb,height,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) present
  exact ⟨j,lo,hi,unpaid,⟨x,y,pa,pb,height,red,blue,w⟩,lost⟩

#print axioms ten_actual_columns_below_inventory
#print axioms ten_actual_missing_threshold
end JSP452Audit.StarHost
