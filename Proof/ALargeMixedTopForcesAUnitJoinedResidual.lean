import SumOfMatchingAxisLossesOnTheTwoPortGraphs
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_nonunit_joined_covers_lower (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity)
    (nz : 0<originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.chosen) F.n)
      R.roots.ncard R.totalCapacity) 2) (j : ℕ) (lo : 2≤j) :
    2*widthAt F.n F.m F.r j≤R.jointPrice j+R.axisAllowance F.n F.m F.r j := by
  classical
  let W := componentBudget (F.G.induce R.chosen) F.n
  let J := commonErasedDemand F.n W R.roots.ncard R.totalCapacity
  change 0<originalThresholdCount J 2 at nz
  by_cases free : 2*widthAt F.n F.m F.r j≤R.jointPrice j
  · exact free.trans (Nat.le_add_right _ _)
  have price := nine_actual_residual_columns_below_inventory F paid nine R long j (by omega)
  have lost : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by omega
  have live : 0<widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,height,red,blue,area⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) live
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,height,red,blue,area⟩
  have budgets := nine_long_side_actual_source_prices F paid nine R long
  have absent := (missing_threshold_of_two_budget_columns F.n F.m F.hn F.hm F.pn W budgets.2.2.1 budgets.1 lost x y win).2.1
  change originalThresholdCount J x=0 at absent
  rcases strict_nine_single_short_unpaid_kinds F paid nine R long short j x y lost win with ⟨rfl,rfl⟩|⟨rfl,_⟩
  · have hi : 3≤x := by
      by_contra! small
      have eq : x=2 := by omega
      rw [eq] at absent;omega
    have eq : R.axisAllowance F.n F.m F.r x=2*widthAt F.n F.m F.r x-R.jointPrice x := if_pos ⟨hi,win⟩
    rw [eq];omega
  · omega

theorem strict_nine_large_top_forces_joined_units (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight F.n F.m F.r 9 x y) :
    originalThresholdCount (commonErasedDemand F.n (componentBudget (F.G.induce R.chosen) F.n)
      R.roots.ncard R.totalCapacity) 2=0 := by
  by_contra! nz
  have half := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
  have space : F.t+2*(∑j,(F.m j-1)/2)≤R.totalCapacity := by
    have dp := (strict_nine_root_deleted_row F paid nine R).1
    omega
  have sum := R.all_axis_allowances F.n F.m F.ht F.hn F.hm F.pn F.pm F.row space
  have top := strict_nine_single_short_large_top_price F paid nine R short winner
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let X := ∑i,(F.n i-1)/2
  let L := widthAt F.n F.m F.r
  have last : 2*L 9+2*X+2*d≤R.jointPrice 9 := by
    change 2*L 9+2*X+2*d≤R.roots.ncard+2*R.totalCapacity at top
    exact top.trans (by dsimp only [NinePortRegion.jointPrice];omega)
  have total := fold_top_layer_payment 9 d X L R.jointPrice (R.axisAllowance F.n F.m F.r) (by decide) last
    (fun j lo _ => strict_nine_nonunit_joined_covers_lower F paid nine R long short (Nat.pos_of_ne_zero nz) j lo) sum
  apply strict_nine_joint_allowance_six_impossible F paid nine R aligned
  change 2*(∑i∈Finset.range 8,L (i+2))+2*d≤(∑i∈Finset.range 8,R.jointPrice (i+2))+6
  change 2*(∑i∈Finset.range 8,L (i+2))+2*d≤(∑i∈Finset.range 8,R.jointPrice (i+2)) at total
  omega

#print axioms strict_nine_nonunit_joined_covers_lower
#print axioms strict_nine_large_top_forces_joined_units
end JSP452Audit.StarHost
