import TheOriginalVolumeOfTheTwoPortBoxes
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem nine_axis_pays_by_allowance {s t r j : ℕ} {X : Type*} [Finite X] {G : SimpleGraph X}
    (R : NinePortRegion G) (n : Fin s→ℕ) (m : Fin t→ℕ) (high : 3≤j) (win : WinsHeight n m r j j 1) :
    2*widthAt n m r j≤R.jointPrice j+R.axisAllowance n m r j := by
  classical
  rw [NinePortRegion.axisAllowance,if_pos ⟨high,win⟩];omega

theorem strict_nine_no_two_head_column_paid (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) (j : ℕ) (lo : 2≤j)
    (no : ¬∃y,WinsHeight F.n F.m F.r j 2 y) :
    2*widthAt F.n F.m F.r j≤R.jointPrice j+R.axisAllowance F.n F.m F.r j := by
  by_cases ok : 2*widthAt F.n F.m F.r j≤R.jointPrice j
  · omega
  have bounds := nine_actual_residual_columns_below_inventory F paid nine R long j (by omega)
  have loss : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,h,r,b,s⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) (by omega : 0<widthAt F.n F.m F.r j)
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,h,r,b,s⟩
  rcases strict_nine_single_short_unpaid_kinds F paid nine R long short j x y loss win with ⟨rfl,rfl⟩|⟨rfl,_⟩
  · have high : 3≤x := by
      by_contra! small
      have eq : x=2 := by omega
      subst x;exact no ⟨1,win⟩
    exact nine_axis_pays_by_allowance R F.n F.m high win
  · exact (no ⟨y,win⟩).elim

theorem strict_nine_higher_boundary_cost (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<F.s) (short : F.t≤R.totalCapacity) (j : ℕ) (high : 4≤j)
    (few : originalThresholdCount F.n 2≤R.totalCapacity) :
    2*widthAt F.n F.m F.r j≤R.jointPrice j+R.axisAllowance F.n F.m F.r j+
      (if j=F.m ⟨0,F.ht⟩+1 then 2 else 0) := by
  by_cases ok : 2*widthAt F.n F.m F.r j≤R.jointPrice j
  · omega
  have bounds := nine_actual_residual_columns_below_inventory F paid nine R long j (by omega)
  have loss : R.basicPrice F.n F.m F.r j<2*widthAt F.n F.m F.r j := by omega
  obtain ⟨x,y,px,py,h,r,b,s⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
    (by omega : 0<j) (by omega : 0<widthAt F.n F.m F.r j)
  have win : WinsHeight F.n F.m F.r j x y := ⟨px,py,h,r,b,s⟩
  rcases strict_nine_single_short_unpaid_kinds F paid nine R long short j x y loss win with ⟨rfl,rfl⟩|⟨rfl,_,last⟩
  · exact (nine_axis_pays_by_allowance R F.n F.m (by omega) win).trans (Nat.le_add_right _ _)
  · rcases last with low|⟨yb,jb⟩
    · omega
    · obtain ⟨_,mc,_⟩ := strict_only_double_escape F paid
      have cap := mc ⟨0,F.ht⟩
      rw [nine] at cap
      have maxB := large_blue_peak_prefix F.hs F.ht F.n F.m F.hn F.hm F.live (by omega : diagonal F.n F.m (F.r+2)=9+1) cap.le
      have hwidth := (strict_nine_original_peak F paid nine).2.1
      rw [if_pos jb]
      rw [yb] at s
      dsimp only [NinePortRegion.jointPrice];omega

theorem strict_nine_matching_axis_qbound (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (short : F.t≤R.totalCapacity) (j : ℕ) (positive : 0<j) (win : WinsHeight F.n F.m F.r j j 1) :
    let Y := ∑i,(F.m i-1)/2
    let q := R.totalCapacity-(F.t+2*Y)+1
    2*widthAt F.n F.m F.r j≤R.jointPrice j+2*q := by
  intro Y q
  let P := R.totalCapacity
  let w := P+1-(F.t+Y)
  have price := ((strict_nine_short_box_endpoint F paid nine R).2 short).2.2
  have pos := (strict_nine_root_deleted_row F paid nine R).1
  have space : F.t+2*Y≤P := by change F.t+2*Y+_≤P+1 at price;omega
  have total := full_half_order_identity F.m F.pm
  change (∑i,(F.m i+1)/2)=F.t+Y at total
  have fits : w≤P := by dsimp only [w];have := F.ht;omega
  have big : P-w<∑j,(F.m j+1)/2 := by dsimp only [w];omega
  have inventory := R.two_real_axis_inventories F.n F.m F.ht F.hn F.hm F.pn F.pm F.row w fits big j positive
  have width := win.2.2.2.2.2
  rw [original_threshold_one F.m F.pm] at width
  rw [width]
  change 2*(originalThresholdCount F.n j+F.t-1-F.r)≤R.roots.ncard+2*P+
    uniformEnvelope (F.G.induce R.outside) j+uniformEnvelope R.retainedEdges j+2*(P-(F.t+2*Y)+1)
  exact matching_axis_qbound _ _ _ _ _ _ w 1 _ _ space F.ht rfl (by decide)
    (fun _ => by simpa only [Nat.add_sub_cancel] using inventory)

#print axioms nine_axis_pays_by_allowance
#print axioms strict_nine_no_two_head_column_paid
#print axioms strict_nine_higher_boundary_cost
#print axioms strict_nine_matching_axis_qbound
end JSP452Audit.StarHost
