import TheTotalMatchingAxisLossOnTheTenDegreeRows
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_nonunit_joined_covers_lower (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1) (long : R.capacity<F.s) (short : F.t≤R.capacity)
    (nz : 0<originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.core) F.n)
      R.roots.ncard R.capacity) 2) (j : ℕ) (lo : 2≤j) :
    2*widthAt F.n F.m F.r j≤R.jointPrice j+R.axisAllowance F.n F.m F.r j := by
  classical
  let W := componentBudget (F.G.induce R.core) F.n
  let J := commonErasedDemand F.n W R.roots.ncard R.capacity
  change 0<originalThresholdCount J 2 at nz
  by_cases free : 2*widthAt F.n F.m F.r j≤R.jointPrice j
  · exact free.trans (Nat.le_add_right _ _)
  have price := ten_actual_columns_below_inventory F paid ten R small (by omega) long j (by omega)
  have lost : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by omega
  have live : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,height,red,blue,area⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) live
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,height,red,blue,area⟩
  have budgets := ten_long_side_two_prices F paid ten R small (by omega) long
  have absent := (missing_threshold_of_two_budget_columns F.n F.m F.hn F.hm F.pn W budgets.2.2.1 budgets.1 lost x y win).2.1
  change originalThresholdCount J x=0 at absent
  rcases ten_single_short_unpaid_kinds F paid ten R small (by omega) balanced long short j x y lost win with ⟨rfl,rfl⟩|⟨rfl,_⟩
  · have hi : 3≤x := by
      by_contra! tiny
      have eq : x=2 := by omega
      rw [eq] at absent;omega
    have eq : R.axisAllowance F.n F.m F.r x=2*widthAt F.n F.m F.r x-R.jointPrice x := if_pos ⟨hi,win⟩
    rw [eq];omega
  · omega

theorem ten_large_top_forces_joined_units (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1) (long : R.capacity<F.s) (short : F.t≤R.capacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 10 x y) :
    originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.core) F.n)
      R.roots.ncard R.capacity) 2=0 := by
  by_contra! nz
  have half := ((ten_short_core_endpoint F paid R).2 short).2.2
  have space : F.t+2*(∑j,(F.m j-1)/2)≤R.capacity := by
    have dp := (ten_physical_root_deleted_row F paid R).1
    omega
  have sum := R.all_axis_allowances F.n F.m F.ht F.hn F.hm F.pn F.pm F.row space
  have top := ten_single_short_large_top_price F paid ten R balanced short winner
  let d := F.rank-matchingEdges F.G
  let X := ∑i,(F.n i-1)/2
  let L := widthAt F.n F.m F.r
  have last : 2*L 10+2*X+2*d≤R.jointPrice 10 := by
    change 2*L 10+2*X+2*d≤R.roots.ncard+2*R.capacity at top
    exact top.trans (by dsimp only [TenBlockPartition.jointPrice];omega)
  have total := fold_top_layer_payment 10 d X L R.jointPrice (R.axisAllowance F.n F.m F.r) (by decide) last
    (fun j lo _ => ten_nonunit_joined_covers_lower F paid ten R small excess balanced long short (Nat.pos_of_ne_zero nz) j lo) sum
  apply ten_joint_payment_impossible F paid ten R 0 (by omega)
  change 2*(∑i∈Finset.range 9,L (i+2))+2*d≤(∑i∈Finset.range 9,R.jointPrice (i+2))+0
  exact total

#print axioms ten_nonunit_joined_covers_lower
#print axioms ten_large_top_forces_joined_units
end JSP452Audit.StarHost
