import TwoHeadFeesInTheActualNineCut
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_last_boundary_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (aligned : (highestWidth F.n F.m F.r:ℤ)≤R.K.eta)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) : False := by
  let a := R.roots.ncard
  let P := R.totalCapacity
  let W := componentBudget (F.G.induce R.chosen) F.n
  let J := commonErasedDemand F.n W a P
  let v := originalThresholdCount (W.entries F.n) 2
  let f := originalThresholdCount F.n 2
  let V := P-f
  let u := F.s-f
  let delta := P-W.loss
  let d := F.rank-matchingEdges F.G-R.rankAllowance
  let L := widthAt F.n F.m F.r
  let C := R.basicPrice F.n F.m F.r
  let g := originalThresholdCount F.m
  let h := highestWidth F.n F.m F.r
  have cap (x:F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have rank := (R.region_rank_edges cap).1
  have boundary := strict_nine_single_short_only_two_eight F paid nine R aligned long short
  have few := strict_nine_final_few_nonunits F paid nine R aligned long short
  change f≤P at few
  have ar : 1≤a := R.root_count.1
  have dd : 2≤d := (strict_nine_root_deleted_row F paid nine R).1
  have top : diagonal F.n F.m (F.r+2)=9+1 := by omega
  have vol := nine_removal_volume_guard R F.n F.pn
  change matchingEdges (F.G.induce R.chosen)≤u+2+3*(matchingEdges (F.G.induce R.chosen)-W.loss) at vol
  rw [rank] at vol
  change P≤u+2+3*delta at vol
  have guard := (nine_long_side_exterior_endpoints F paid nine R long).1
  change a+F.r+2*(d+_)+delta≤F.s-P at guard
  change P<F.s at long
  have tail : V+a+F.r+2*d+delta≤u := by dsimp only [V,u];omega
  have units (empty:v=0) : P≤3*V+a+1 := by
    have b := nine_all_units_bound F.G R F.n F.hn long rank empty
    change P≤3*V+2 at b
    omega
  have active (j : ℕ) (small : j≤8) : 0<g j := by
    have eq := boundary.1
    exact Nat.zero_lt_of_lt ((original_threshold_prefix F.m F.hm j ⟨0,F.ht⟩).1 (by omega))
  have sparse : g 8≤F.r := boundary.2.2.2
  have present (j : ℕ) (hi : j≤9) : 0<L j := actual_height_positive F.n F.m F.live top j (by omega)
  have floor : a+2*P≤C 9 := by
    change a+2*P≤a+2*P+widthAt (W.entries F.n) F.m (F.r+a) 9+widthAt J F.m F.r 9
    omega
  have last := boundary.2.1.2.2.2.2.2
  change L 9=f+g 8-1-F.r at last
  have topFee : 2*L 9+a+2*V+2*F.r+2≤C 9+2*g 8 := by
    have pos := present 9 (by decide)
    dsimp only [V];omega
  have kind := strict_nine_last_boundary_gap_kind F paid nine R aligned long short
  have fee (j : ℕ) (lo : 2≤j) (hi : j≤8) (gap:C j<2*L j) :
      2*L j+2*(u+delta+g j)≤C j+2*g (j-1) ∧
      (0<v → 2*L j+V+v+u+delta+g j≤C j+g (j-1)) := by
    have w := (kind j lo (by omega) gap).1
    have q := nine_raw_two_head_fee F.G R F.n F.m F.r j (j-1) F.hn F.hm F.pn
      long rank (active j hi) w (present j (by omega)) few
    change 2*L j+2*(u+delta+g j)≤C j+2*g (j-1) ∧ (0<v → 2*L j+(V+v)+u+delta+g j≤C j+g (j-1)) at q
    exact ⟨q.1,fun pos => by have second := q.2 pos;omega⟩
  have one : g 1=F.t := original_threshold_one F.m F.pm
  have lower := last_boundary_three_price F.t F.r a P V v u delta d 1 1 6 (g 2) (g 3) (g 8)
    (L 2) (L 3) (L 9) (C 2) (C 3) (C 9) (by decide) dd (by omega)
    ⟨threshold_anti_height F.m (by decide : 3≤8),threshold_anti_height F.m (by decide : 2≤3),
      original_threshold_le_length F.m 2⟩ short (by decide) (by omega) tail units topFee
    (fun gap => by simpa only [show 2-1=1 by decide,one] using fee 2 (by decide) (by decide) gap)
    (fun gap => by simpa only [show 3-1=2 by decide] using fee 3 (by decide) (by decide) gap)
  have hp : 1≤h := (strict_nine_original_peak F paid nine).1
  have hn : h≤2 := (strict_nine_original_peak F paid nine).2.1
  have three : 2*L 2+2*L 3+2*L 9+2*h≤C 2+C 3+C 9+9*1+2*delta := by omega
  have rest (j : ℕ) (lo : 4≤j) (hi : j<9) : 2*L j≤C j := by
    by_contra! gap
    rcases (kind j (by omega) (by omega) gap).2 with hh|hh|hh <;> omega
  have total := fold_last_three_prices 9 h 1 delta L C (by decide) three rest
  change 2*interiorArea F.n F.m F.r 9+2*h≤(∑j∈Finset.range 8,C (j+2))+9+2*delta at total
  have account := strict_nine_joint_residual_area F paid nine R long
  have sumPrice := R.basic_price_sum F.n F.m F.r
  change (∑j∈Finset.range 8,C (j+2))=_ at sumPrice
  change 8*(a+2*P)+interiorArea (W.entries F.n) F.m (F.r+a) 9+interiorArea J F.m F.r 9+16+2*delta<
    2*interiorArea F.n F.m F.r 9+2*h+R.rootDebt at account
  rw [←sumPrice] at account
  have debt := (R.root_deleted_edge_account cap).2
  change (h:ℤ)≤R.K.eta at aligned
  omega

#print axioms strict_nine_last_boundary_impossible
end JSP452Audit.StarHost
