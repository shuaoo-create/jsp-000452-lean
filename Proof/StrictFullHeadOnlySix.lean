import FiniteFullSingleActualExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_full_head_only_six (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D ∨ F.m ⟨0,F.ht⟩=D) → D=6 := by
  intro D heads
  let d := F.rank-matchingEdges F.G
  let μ := matchingEdges (F.G.induce K.core)
  let a := K.roots.ncard
  have low : 6≤D := strict_source_degree_at_least_six F paid
  have high : D≤14 := strict_full_degree_at_most_fourteen F paid K heads
  by_contra notSix
  have deg : 7≤D ∧ D≤14 := by clear * - low high notSix;omega
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];clear * - less;omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have root := strict_source_region_root_budget F paid K
  change D*minimumExposure F.G D+rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
    crossCount F.G K.roots K.rest+2≤2*highestWidth F.n F.m F.r+2*(D/2)*(D/2+1) at root
  have bound : D*minimumExposure F.G D+rootShortfall F.G K.roots D+2≤2*highestWidth F.n F.m F.r+2*(D/2)*(D/2+1) :=
    by clear * - root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have sources := strict_common_actual_successors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have nonunit := strict_full_head_nonunit_exterior F paid K
  have halves := strict_full_opposite_at_most_half F paid K
  have mass := strict_source_whole_list_alternatives F K
  rcases heads with red|blue
  · obtain ⟨emb,len,_,_⟩ := unique.1 red
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by clear * - len;omega
    change F.t≤μ at emb
    have inner := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;clear * - emb;omega)).1
    obtain ⟨_,y,lo,_,_,yp,_,_,_⟩ := trigger.1 red
    have yl := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 yp
    exact finite_full_single_exterior_exit F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm deg cap F.live F.row red rfl
      ⟨by clear * - yl lo;omega,halves.1 red⟩ top d rank F.strict (sources.1 esc) esc inner guards.1 width res
      bound (nonunit.1 red) (trigger.1 red)
  · obtain ⟨emb,len,_,_⟩ := unique.2 blue
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by clear * - len;omega
    change F.s≤μ at emb
    have inner := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;clear * - emb;omega)).1
    obtain ⟨_,y,lo,_,_,yp,_,_,_⟩ := trigger.2 blue
    have yl := (original_threshold_prefix F.n F.hn y ⟨0,F.hs⟩).2 yp
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have en := row_energy_colour_swap F.m F.n F.r
    have hw := highest_width_colour_swap F.m F.n F.r
    exact finite_full_single_exterior_exit F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn deg cap (by rw [swap];exact F.live)
      (swap_positive_forcing_row F.G _ _ F.row) blue rfl ⟨by clear * - yl lo;omega,halves.2 blue⟩
      ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [en];exact F.strict)
      (by rw [swap,en];exact sources.2 esc) esc inner guards.2 (by rw [hw];exact width) res (by rw [hw];exact bound)
      (nonunit.2 blue) (trigger.2 blue)

#print axioms strict_full_head_only_six
end JSP452Audit.StarHost