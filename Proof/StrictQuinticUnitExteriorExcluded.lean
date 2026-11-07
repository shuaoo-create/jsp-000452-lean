import QuinticLargeUnitActualPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Every possible quintic source, in either orientation, must have a
genuine nonunit surviving on its full-headed side in every region. -/
theorem strict_quintic_exterior_nonunit (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (five : diagonal F.n F.m (F.r+2)-1=5) (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let H := F.G.induce K.core
    (F.n ⟨0,F.hs⟩=5 → 0<originalThresholdCount ((componentBudget H F.n).entries F.n) 2) ∧
    (F.m ⟨0,F.ht⟩=5 → 0<originalThresholdCount ((componentBudget H F.m).entries F.m) 2) := by
  intro H
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  let a := K.roots.ncard
  let μ := matchingEdges H
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  have root := ((low_degree_original_costs F paid K).2.2 five).2.1
  have cost : 3*minimumExposure F.G D+rootShortfall F.G K.roots D≤10 := by
    change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤10 at root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have data := strict_both_complete_exteriors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have heads := (strict_quintic_heads_and_positive_offset F paid five).2
  have bad := F.strict
  constructor
  · intro red
    have full := red.trans five.symm
    have h : F.m ⟨0,F.ht⟩=3 ∨ F.m ⟨0,F.ht⟩=4 := by rcases heads with p|p <;> omega
    obtain ⟨_,len,_,_⟩ := unique.1 full
    change μ+a+F.r+d+1≤F.s at len
    have esc : μ<F.s := by omega
    have ext := outer.1 esc
    change a+F.r+2*(d+_)+_≤F.s-μ at ext
    by_contra neg
    have unit : originalThresholdCount ((componentBudget H F.n).entries F.n) 2=0 := by omega
    have fee := quintic_full_unit_large_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm five cap F.live full
      h top d rank (data.1 esc) esc guards.1 (by change a+F.r+2*d≤F.s-μ;omega) width res cost (trigger.1 full) unit
    omega
  · intro blue
    have full := blue.trans five.symm
    have h : F.n ⟨0,F.hs⟩=3 ∨ F.n ⟨0,F.hs⟩=4 := by rcases heads with p|p <;> omega
    obtain ⟨_,len,_,_⟩ := unique.2 full
    change μ+a+F.r+d+1≤F.t at len
    have esc : μ<F.t := by omega
    have ext := outer.2 esc
    change a+F.r+2*(d+_)+_≤F.t-μ at ext
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have Hswap := highest_width_colour_swap F.m F.n F.r
    by_contra neg
    have unit : originalThresholdCount ((componentBudget H F.m).entries F.m) 2=0 := by omega
    have fee := quintic_full_unit_large_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn five cap (by rw [swap];exact F.live)
      full h ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [swap];exact data.2 esc) esc guards.2
      (by change a+F.r+2*d≤F.t-μ;omega) (by rw [Hswap];exact width) res cost (trigger.2 full) unit
    rw [row_energy_colour_swap F.m F.n] at fee;omega

#print axioms strict_quintic_exterior_nonunit
end JSP452Audit.StarHost