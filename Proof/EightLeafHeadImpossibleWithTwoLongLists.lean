import WhatEachUnitAxisCostsOnOneActualHistory
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_two_long_has_mixed_low_winner (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) :
    ∃j a b,2≤j ∧ j≤8 ∧ 2≤a ∧ 2≤b ∧ WinsHeight F.n F.m F.r j a b := by
  classical
  by_contra absent
  let P := R.totalCapacity
  let L := widthAt F.n F.m F.r
  let h := highestWidth F.n F.m F.r
  obtain ⟨H⟩ := three_degree_stages_exist R.erased 7
  let B := H.upper
  let b := B.ncard
  have cap := nine_erased_degree_cap F paid nine R
  have low := (H.degree_caps cap).1
  obtain ⟨S,tail⟩ := complete_degree_cut_account 8 (R.erased.induce Bᶜ) low
  obtain ⟨T,top,hist⟩ := extend_history_by_first_stage R.erased 8 B H.first cap S tail
  change T 9=B at top
  have start := (nine_erased_unit_axis_counts F paid R long T hist).1
  have each (j) (lo : 2≤j) (hi : j≤8) : L j≤P+(T j).ncard := by
    by_cases alive : 0<L j
    · obtain ⟨a,b,pa,pb,height,red,blue,w⟩ := original_column_real_winner F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm
        (by omega : 0<j) alive
      have win : WinsHeight F.n F.m F.r j a b := ⟨pa,pb,height,red,blue,w⟩
      have axis : a=1 ∨ b=1 := by
        by_contra! no
        exact absent ⟨j,a,b,lo,hi,by omega,by omega,win⟩
      exact nine_unit_winner_on_history F paid R long T hist j a b (by omega) (by omega) win axis
    · omega
  have combined := Finset.sum_le_sum (s:=Finset.range 7) (fun i m => each (i+2) (by omega)
    (by have := Finset.mem_range.mp m;omega))
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,nsmul_eq_mul,Nat.cast_id] at combined
  let lowArea := ∑i∈Finset.range 7,L (i+2)
  let covered := ∑i∈Finset.range 7,(T (i+2)).ncard
  change lowArea≤7*P+covered at combined
  have tally : R.erased.edgeSet.ncard=(T 1).ncard+covered+b := by
    have edges := hist.2
    change R.erased.edgeSet.ncard=∑i∈Finset.range 9,(T (i+1)).ncard at edges
    rw [Finset.sum_range_succ,show 8+1=9 by decide,top,Finset.sum_range_succ'] at edges
    change R.erased.edgeSet.ncard=covered+(T 1).ncard+b at edges
    omega
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=9) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+(∑i∈Finset.range 8,L (i+2))+h at area
  rw [Finset.sum_range_succ] at area
  change rowEnergy F.n F.m F.r=F.rank+(lowArea+L 9)+h at area
  have capG (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have fee := (R.adapted_edge_account capG).2.2
  change F.G.edgeSet.ncard=R.erased.edgeSet.ncard+9*P+8+R.portCount at fee
  have col := (strict_nine_first_exterior_eight_bound F paid nine R long H).2
  change L 9-b≤R.slotDamage 2+7 at col
  have slot := R.port_slot_sizes.1
  change 3*R.slotDamage 2≤2*P+4+R.portCount at slot
  have narrow : h≤2 := (strict_nine_original_peak F paid nine).2.1
  have strict := F.strict
  change F.rank≤P+(T 1).ncard at start
  have many : 10≤P := by
    have c0 := (R.inner 0).2;have c1 := (R.inner 1).2
    change 5≤R.capacity 0 at c0;change 5≤R.capacity 1 at c1;change 10≤R.capacity 0+R.capacity 1;omega
  omega

theorem strict_nine_two_long_heads_at_most_seven (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G)
    (long : R.totalCapacity<min F.s F.t) : (∀i,F.n i≤7) ∧ (∀j,F.m j≤7) := by
  obtain ⟨j,a,b,lo,hi,ra,bb,win⟩ := strict_nine_two_long_has_mixed_low_winner F paid nine R long
  have forbid := strict_eight_head_no_mixed_nine_low_winner F paid nine R long
  constructor
  · intro i;by_contra! large
    have count := (original_threshold_prefix F.n F.hn 8 i).mp large
    exact forbid (Or.inl (Nat.zero_lt_of_lt count)) j a b lo hi ra bb win
  · intro i;by_contra! large
    have count := (original_threshold_prefix F.m F.hm 8 i).mp large
    exact forbid (Or.inr (Nat.zero_lt_of_lt count)) j a b lo hi ra bb win

#print axioms strict_nine_two_long_has_mixed_low_winner
#print axioms strict_nine_two_long_heads_at_most_seven
end JSP452Audit.StarHost
