import FullPureAxisThresholdRange
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_full_head_genuine_pure_range (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D → 3≤F.m ⟨0,F.ht⟩ → LocalPureWitness F.G K F.n F.m F.ht F.r) ∧
    (F.m ⟨0,F.ht⟩=D → 3≤F.n ⟨0,F.hs⟩ → LocalPureWitness F.G K F.m F.n F.hs F.r) := by
  intro D
  let d := F.rank-matchingEdges F.G
  let μ := matchingEdges (F.G.induce K.core)
  let a := K.roots.ncard
  have deg : 6≤D := strict_source_degree_at_least_six F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have res := (minimal_strict_source_deficit F paid).2.1
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have sources := strict_common_actual_successors F paid K
  have kinds := strict_single_unpaid_types F paid K
  have missing := strict_source_missing_heights F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have mass := strict_source_whole_list_alternatives F K
  constructor
  · intro red large
    obtain ⟨emb,len,_,sub⟩ := unique.1 red
    have b := sub ⟨0,F.ht⟩
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    change F.t≤μ at emb
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    have pure := actual_pure_axis_needed F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm F.live deg cap top red large b
      d width res (outer.1 esc) esc emb guards.1 (trigger.1 red) (kinds.1 esc emb) (missing.1 esc) (sources.1 esc)
    exact bound_unpaid_pure_location F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm top red large b d (by omega)
      esc (by change F.t+d≤μ+1;omega) pure
  · intro blue large
    obtain ⟨emb,len,_,sub⟩ := unique.2 blue
    have b := sub ⟨0,F.hs⟩
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    change F.s≤μ at emb
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have H := highest_width_colour_swap F.m F.n F.r
    have tp := (diagonal_swap F.m F.n (F.r+2)).trans top
    have pure := actual_pure_axis_needed F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn (by rw [swap];exact F.live)
      deg cap tp blue large b d (H.le.trans width) res (outer.2 esc) esc emb guards.2 (trigger.2 blue)
      (kinds.2 esc emb) (missing.2 esc) (by rw [swap,row_energy_colour_swap F.m F.n];exact sources.2 esc)
    exact bound_unpaid_pure_location F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn tp blue large b d
      (by rw [H];omega) esc (by change F.s+d≤μ+1;omega) pure

#print axioms strict_full_head_genuine_pure_range
end JSP452Audit.StarHost