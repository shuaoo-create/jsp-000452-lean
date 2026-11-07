import ThreeActualBoundaryPricesWithTheCoreDefect
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_short_oriented_partition_impossible (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G)
    (small:R.epsilon≤2) (excess:highestWidth F.n F.m F.r+2+R.epsilon≤R.eta)
    (balanced:R.eta≤F.rank-matchingEdges F.G+1)
    (long : R.capacity<F.s) (short : F.t≤R.capacity) : False := by
  let a := R.roots.ncard
  let P := R.capacity
  let W := componentBudget (F.G.induce R.core) F.n
  let J := commonErasedDemand F.n W a P
  let v := originalThresholdCount (W.entries F.n) 2
  let f := originalThresholdCount F.n 2
  let V := P-f
  let u := F.s-f
  let delta := P-W.loss
  let d := F.rank-matchingEdges F.G
  let L := widthAt F.n F.m F.r
  let C := R.basicPrice F.n F.m F.r
  let g := originalThresholdCount F.m
  let h := highestWidth F.n F.m F.r
  have boundary := ten_single_short_only_two_nine F paid ten R small excess balanced long short
  have few := ten_final_few_nonunits F paid ten R small excess balanced long short
  change f≤P at few
  have dd : 2≤d := (ten_physical_root_deleted_row F paid R).1
  have top : diagonal F.n F.m (F.r+2)=10+1 := by omega
  have vol := ten_removal_volume_guard R F.n F.pn
  change P≤u+a+R.eta+3*delta at vol
  have guard := (ten_long_side_exterior_endpoints F paid ten R small (by omega) long).1
  change a+F.r+2*(d+_)+delta≤F.s-P at guard
  change P<F.s at long
  have tail : V+a+F.r+2*d+delta≤u := by dsimp only [V,u];omega
  have units (empty:v=0) : P≤3*V+a+R.eta := ten_all_units_bound F.G R F.n F.hn long empty
  have active (j : ℕ) (small : j≤9) : 0<g j := by
    have eq := boundary.1
    exact Nat.zero_lt_of_lt ((original_threshold_prefix F.m F.hm j ⟨0,F.ht⟩).1 (by omega))
  have sparse : g 9≤F.r+h := boundary.2.2.2
  have present (j : ℕ) (hi : j≤10) : 0<L j := actual_height_positive F.n F.m F.live top j (by omega)
  have floor : a+2*P≤C 10 := by
    change a+2*P≤a+2*P+widthAt (W.entries F.n) F.m (F.r+a) 10+widthAt J F.m F.r 10
    omega
  have last := boundary.2.1.2.2.2.2.2
  change L 10=f+g 9-1-F.r at last
  have topFee : 2*L 10+a+2*V+2*F.r+2≤C 10+2*g 9 := by
    have pos := present 10 (by decide)
    dsimp only [V];omega
  have kind := ten_last_boundary_gap_kind F paid ten R small excess balanced long short
  have fee (j : ℕ) (lo : 2≤j) (hi : j≤9) (gap:C j<2*L j) :
      2*L j+2*(u+delta+g j)≤C j+2*g (j-1) ∧
      (0<v → 2*L j+V+v+u+delta+g j≤C j+g (j-1)) := by
    have w := (kind j lo (by omega) gap).1
    have q := ten_raw_two_head_fee F.G R F.n F.m F.r j (j-1) F.hn F.hm F.pn
      long (active j hi) w (present j (by omega)) few
    change 2*L j+2*(u+delta+g j)≤C j+2*g (j-1) ∧ (0<v → 2*L j+(V+v)+u+delta+g j≤C j+g (j-1)) at q
    exact ⟨q.1,fun pos => by have second := q.2 pos;omega⟩
  have one : g 1=F.t := original_threshold_one F.m F.pm
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  have lower := last_boundary_with_core_defect F.t F.r a P V v u delta d R.eta h (8*R.eta) (g 2) (g 3) (g 9)
    (L 2) (L 3) (L 10) (C 2) (C 3) (C 10) (by dsimp only [h];omega) balanced (by dsimp only [h] at *;omega)
    ⟨threshold_anti_height F.m (by decide : 3≤9),threshold_anti_height F.m (by decide : 2≤3),
      original_threshold_le_length F.m 2⟩ short (by dsimp only [h] at hp;omega) vol tail units topFee
    (fun gap => by simpa only [show 2-1=1 by decide,one] using fee 2 (by decide) (by decide) gap)
    (fun gap => by simpa only [show 3-1=2 by decide] using fee 3 (by decide) (by decide) gap)
  have rest (j : ℕ) (lo : 4≤j) (hi : j<10) : 2*L j≤C j := by
    by_contra! gap
    rcases (kind j (by omega) (by omega) gap).2 with hh|hh|hh <;> omega
  have total := fold_last_three_with_fee 10 h (8*R.eta) delta L C (by decide) lower rest
  change 2*interiorArea F.n F.m F.r 10+2*h≤(∑j∈Finset.range 9,C (j+2))+8*R.eta+2*delta at total
  have account := ten_joint_residual_area F paid ten R small (by omega) long
  change (∑j∈Finset.range 9,C (j+2))+10*R.eta+_+_+2*delta<2*interiorArea F.n F.m F.r 10+2*h+R.epsilon at account
  omega

#print axioms ten_short_oriented_partition_impossible
end JSP452Audit.StarHost
