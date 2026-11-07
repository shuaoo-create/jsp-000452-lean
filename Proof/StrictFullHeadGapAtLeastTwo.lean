import FullLastOppositeActualExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_full_opposite_gap_two (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D → F.m ⟨0,F.ht⟩+2≤D) ∧ (F.m ⟨0,F.ht⟩=D → F.n ⟨0,F.hs⟩+2≤D) := by
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
  · intro red
    obtain ⟨emb,len,_,sub⟩ := unique.1 red
    have b := sub ⟨0,F.ht⟩
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    change F.t≤μ at emb
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    by_contra! small
    exact full_last_opposite_impossible F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm deg cap F.live red
      (by omega) top d (sources.1 esc) esc (by change F.t+d≤μ+1;omega) guards.1 (outer.1 esc) width res
      (trigger.1 red) (kinds.1 esc emb) (missing.1 esc)
  · intro blue
    obtain ⟨emb,len,_,sub⟩ := unique.2 blue
    have b := sub ⟨0,F.hs⟩
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    change F.s≤μ at emb
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    by_contra! small
    exact full_last_opposite_impossible F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn deg cap (by rw [swap];exact F.live)
      blue (by omega) ((diagonal_swap _ _ _).trans top) d (by rw [swap,row_energy_colour_swap F.m F.n];exact sources.2 esc)
      esc (by change F.s+d≤μ+1;omega) guards.2 (outer.2 esc) ((highest_width_colour_swap _ _ _).le.trans width)
      res (trigger.2 blue) (kinds.2 esc emb) (missing.2 esc)

#print axioms strict_full_opposite_gap_two
end JSP452Audit.StarHost