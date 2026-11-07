import FullSevenHighActualExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_full_has_at_most_six_high_layers (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D → D≤F.m ⟨0,F.ht⟩+7) ∧ (F.m ⟨0,F.ht⟩=D → D≤F.n ⟨0,F.hs⟩+7) := by
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
  have trigger := strict_full_mixed_boundary F paid K
  have nonunit := strict_full_head_nonunit_exterior F paid K
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];have less := (minimal_rank_exact_source F paid).2.2.1;clear * - less;omega
  have mass := strict_source_whole_list_alternatives F K
  constructor
  · intro red
    obtain ⟨emb,len,_,sub⟩ := unique.1 red
    have b := sub ⟨0,F.ht⟩
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by clear * - len;omega
    change F.t≤μ at emb
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;clear * - emb;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    obtain ⟨_,y,yl,_,_,yp,_,_,_⟩ := trigger.1 red
    have bh := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 yp
    by_contra! small
    have high : 9≤D := by clear * - yl bh small;omega
    have outerFee := outer.1 esc
    change a+F.r+2*(d+_)+_≤F.s-μ at outerFee
    exact seven_high_full_impossible F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm high cap F.live F.row red rfl
      (by clear * - yl bh;omega) (by clear * - small;omega) top d rank F.strict (sources.1 esc) esc half guards.1
      (by change a+F.r+2*d≤F.s-μ;clear * - outerFee;omega) width res (nonunit.1 red)
  · intro blue
    obtain ⟨emb,len,_,sub⟩ := unique.2 blue
    have b := sub ⟨0,F.hs⟩
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by clear * - len;omega
    change F.s≤μ at emb
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;clear * - emb;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    obtain ⟨_,y,yl,_,_,yp,_,_,_⟩ := trigger.2 blue
    have bh := (original_threshold_prefix F.n F.hn y ⟨0,F.hs⟩).2 yp
    by_contra! small
    have high : 9≤D := by clear * - yl bh small;omega
    have outerFee := outer.2 esc
    change a+F.r+2*(d+_)+_≤F.t-μ at outerFee
    have eq := row_energy_colour_swap F.m F.n F.r
    exact seven_high_full_impossible F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn high cap (by rw [swap];exact F.live)
      (swap_positive_forcing_row F.G _ _ F.row) blue rfl (by clear * - yl bh;omega) (by clear * - small;omega)
      ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [eq];exact F.strict)
      (by rw [swap,eq];exact sources.2 esc) esc half guards.2 (by change a+F.r+2*d≤F.t-μ;clear * - outerFee;omega)
      ((highest_width_colour_swap _ _ _).le.trans width) res (nonunit.2 blue)

theorem strict_full_degree_at_most_fourteen (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    (F.n ⟨0,F.hs⟩=D ∨ F.m ⟨0,F.ht⟩=D) → D≤14 := by
  intro D head
  have half := strict_full_opposite_at_most_half F paid K
  have bound := strict_full_has_at_most_six_high_layers F paid K
  rcases head with n|m
  · have h := half.1 n;have g := bound.1 n
    change 2*F.m ⟨0,F.ht⟩≤D at h;change D≤F.m ⟨0,F.ht⟩+7 at g;omega
  · have h := half.2 m;have g := bound.2 m
    change 2*F.n ⟨0,F.hs⟩≤D at h;change D≤F.n ⟨0,F.hs⟩+7 at g;omega

#print axioms strict_full_has_at_most_six_high_layers
#print axioms strict_full_degree_at_most_fourteen
end JSP452Audit.StarHost