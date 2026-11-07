import ARealPositiveRankEightDegreeSuccessor
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_first_exterior_eight_bound (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    minimumExposure (R.erased.induce H.upperᶜ) 8≤7 ∧
      widthAt F.n F.m F.r 9-H.upper.ncard≤R.slotDamage 2+7 := by
  obtain ⟨I,_,_,_,_,_,debt,_,transfer,budget⟩ := strict_nine_first_stage_exposure F paid nine R long H
  let S := I∪H.upper
  change (F.G.induce S).edgeSet.ncard+R.portCount≤2 at debt
  change minimumExposure (R.erased.induce H.upperᶜ) 8≤minimumExposure (F.G.induce Sᶜ) 8 at transfer
  change 6*(minimumExposure (F.G.induce Sᶜ) 8:ℤ)≤
    40+2*((highestWidth F.n F.m F.r:ℤ)+(F.G.induce S).edgeSet.ncard-1) at budget
  have narrow := (strict_nine_original_peak F paid nine).2.1
  have bound : minimumExposure (R.erased.induce H.upperᶜ) 8≤7 := by omega
  have col := (strict_nine_general_ninth_column F paid nine R H).2
  exact ⟨bound,by omega⟩

theorem strict_nine_menu_beyond_eight (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (H : ThreeDegreeStages R.erased 7) :
    H.midCut.ncard<portMenuGap R.capacity-(F.r+1) := by
  let k := portMenuGap R.capacity-(F.r+1)
  let P := R.totalCapacity
  let h := highestWidth F.n F.m F.r
  let L := widthAt F.n F.m F.r 9
  let M := R.slotDamage 2
  let b := H.upper.ncard
  change H.midCut.ncard<k
  by_contra! fit
  have count := nested_removed_card H.upper H.middle
  change H.midCut.ncard=b+H.middle.ncard at count
  have short := (strict_nine_actual_stage_inventory F paid nine R H).1
  change b<k at short
  obtain ⟨V,size,cost⟩ := two_stage_exact_prefix R.erased 8 H.upper H.first H.middle H.second k (by omega)
  change R.erased.edgeSet.ncard=(R.erased.induce Vᶜ).edgeSet.ncard+8*k+min k b at cost
  rw [min_eq_right short.le] at cost
  have gap : portMenuGap R.capacity≤F.r+k+1 := by dsimp [k];omega
  have menu := port_menu_of_gap R.capacity (F.r+k) gap
  have row := R.actual_adapted_menu_row _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row V (by rwa [size])
  let q := k+P
  have live := F.live
  have c0 := (R.inner 0).2
  change 5≤R.capacity 0 at c0
  have pos : 0<q := by change 0<k+(R.capacity 0+R.capacity 1);omega
  have small : rowCount F.s F.t (F.r+q)<F.rank := by dsimp [StrictFamily.rank,rowCount] at live ⊢;omega
  have actual : ForcingRow (R.erased.induce Vᶜ) F.s F.t (padDemand F.n) (padDemand F.m) (F.r+q) := by
    simpa [q,P,size,Nat.add_assoc] using row
  have pay := paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ actual small
  have upper := prefix_at_two_top_columns (r:=F.r) F.hs F.ht F.n F.m F.hn F.hm 8 (by omega) q
  change rowEnergy F.n F.m F.r≤rowEnergy F.n F.m (F.r+q)+8*q+L+h at upper
  have cap (x : F.X) := ((minimal_rank_exact_source F paid).2.2.2.1 x).trans_eq nine
  have edge := (R.adapted_edge_account cap).2.2
  change F.G.edgeSet.ncard=R.erased.edgeSet.ncard+9*P+8+R.portCount at edge
  have strict := F.strict
  have narrow : h≤2 := (strict_nine_original_peak F paid nine).2.1
  have col := (strict_nine_first_exterior_eight_bound F paid nine R long H).2
  change L-b≤M+7 at col
  have slot := R.port_slot_sizes.1
  change 3*M≤2*P+4+R.portCount at slot
  have many : 10≤P := by
    have c1 := (R.inner 1).2;change 5≤R.capacity 1 at c1
    change 10≤R.capacity 0+R.capacity 1;omega
  change rowEnergy F.n F.m (F.r+(k+P))≤(R.erased.induce Vᶜ).edgeSet.ncard at pay
  dsimp only [q] at upper
  omega

theorem strict_eight_head_no_mixed_nine_low_winner (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) (head : 0<originalThresholdCount F.n 8 ∨ 0<originalThresholdCount F.m 8)
    (j a b : ℕ) (lo : 2≤j) (hi : j≤8) (wa : 2≤a) (wb : 2≤b) (win : WinsHeight F.n F.m F.r j a b) : False := by
  obtain ⟨H⟩ := three_degree_stages_exist R.erased 7
  exact (Nat.not_le_of_lt (strict_nine_menu_beyond_eight F paid nine R long H))
    (nine_eight_head_mixed_stage_inventory F paid nine R long j a b lo hi head wa wb win H)

#print axioms strict_nine_first_exterior_eight_bound
#print axioms strict_nine_menu_beyond_eight
#print axioms strict_eight_head_no_mixed_nine_low_winner
end JSP452Audit.StarHost
