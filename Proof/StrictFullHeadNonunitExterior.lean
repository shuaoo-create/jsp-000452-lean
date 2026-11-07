import AllDegreeFullUnitJointExit
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- A full original head always leaves a nonunit in every actual ordinary exterior, in either orientation. -/
theorem strict_full_head_nonunit_exterior (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := F.G.induce K.core
    (F.n ⟨0,F.hs⟩=D → 0<originalThresholdCount ((componentBudget H F.n).entries F.n) 2) ∧
    (F.m ⟨0,F.ht⟩=D → 0<originalThresholdCount ((componentBudget H F.m).entries F.m) 2) := by
  intro D H
  let d := F.rank-matchingEdges F.G
  let a := K.roots.ncard
  let μ := matchingEdges H
  have deg : 6≤D := strict_source_degree_at_least_six F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have data := strict_common_actual_successors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have binary := strict_full_binary_nonunit_remaining F paid K
  have bad := F.strict
  constructor
  · intro red
    by_cases two : F.m ⟨0,F.ht⟩=2
    · exact binary.1 red two
    obtain ⟨_,len,_,capB⟩ := unique.1 red
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    have ext := outer.1 esc
    change a+F.r+2*(d+_)+_≤F.s-μ at ext
    obtain ⟨_,y,lo,_,_,present,_,_,_⟩ := trigger.1 red
    have hi := (original_threshold_prefix F.m F.hm y ⟨0,F.ht⟩).2 present
    by_contra no
    have unit : originalThresholdCount ((componentBudget H F.n).entries F.n) 2=0 := by omega
    exact all_full_unit_exteriors_impossible F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm deg cap F.live red
      (by omega) (capB _) top d (data.1 esc) esc guards.1 (by change a+F.r+2*d≤F.s-μ;omega)
      width res (trigger.1 red) unit

  · intro blue
    by_cases two : F.n ⟨0,F.hs⟩=2
    · exact binary.2 blue two
    obtain ⟨_,len,_,capB⟩ := unique.2 blue
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    have ext := outer.2 esc
    change a+F.r+2*(d+_)+_≤F.t-μ at ext
    obtain ⟨_,y,lo,_,_,present,_,_,_⟩ := trigger.2 blue
    have hi := (original_threshold_prefix F.n F.hn y ⟨0,F.hs⟩).2 present
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have Hswap := highest_width_colour_swap F.m F.n F.r
    by_contra no
    have unit : originalThresholdCount ((componentBudget H F.m).entries F.m) 2=0 := by omega
    exact all_full_unit_exteriors_impossible F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn deg cap (by rw [swap];exact F.live)
      blue (by omega) (capB _) ((diagonal_swap _ _ _).trans top) d (by rw [swap,row_energy_colour_swap F.m F.n];exact data.2 esc)
      esc guards.2 (by change a+F.r+2*d≤F.t-μ;omega) (by rw [Hswap];exact width) res (trigger.2 blue) unit


#print axioms strict_full_head_nonunit_exterior
end JSP452Audit.StarHost