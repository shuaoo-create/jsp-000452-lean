import FullBinaryUnitExteriorPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- In either orientation of a minimal source, a full head opposite a
binary head forces at least one nonunit to survive in every ordinary
region's coordinatewise exterior demand. -/
theorem strict_full_binary_nonunit_remaining (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let H := F.G.induce K.core
    (F.n ⟨0,F.hs⟩=D → F.m ⟨0,F.ht⟩=2 →
      0<originalThresholdCount ((componentBudget H F.n).entries F.n) 2) ∧
    (F.m ⟨0,F.ht⟩=D → F.n ⟨0,F.hs⟩=2 →
      0<originalThresholdCount ((componentBudget H F.m).entries F.m) 2) := by
  intro D H
  let d := F.rank-matchingEdges F.G
  let μ := matchingEdges H
  let a := K.roots.ncard
  have deg : 5≤D := strict_source_degree_at_least_five F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have res := (minimal_strict_source_deficit F paid).2.1
  have guard := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have esc := strict_full_head_unique_escape F paid K
  have trigger := strict_full_mixed_boundary F paid K
  have data := strict_both_complete_exteriors F paid K
  have bad := F.strict
  constructor
  · intro red blue
    have len := (esc.1 red).2.1
    change μ+a+F.r+d+1≤F.s at len
    have small : μ<F.s := by omega
    have ext := outer.1 small
    change a+F.r+2*(d+_)+_≤F.s-μ at ext
    have before := guard.1
    change a+F.r+2*(d+_)≤F.t at before
    have dpos : 0<d := by change _+1≤d at res;omega
    by_contra fail
    have zero : originalThresholdCount ((componentBudget H F.n).entries F.n) 2=0 := by omega
    have fee := full_binary_unit_exterior_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm deg cap F.live
      red blue top d rank (data.1 small) small (by omega) (by change a+F.r+2*d≤F.s-μ;omega)
      width res (trigger.1 red) zero
    omega
  · intro blue red
    have len := (esc.2 blue).2.1
    change μ+a+F.r+d+1≤F.t at len
    have small : μ<F.t := by omega
    have ext := outer.2 small
    change a+F.r+2*(d+_)+_≤F.t-μ at ext
    have before := guard.2
    change a+F.r+2*(d+_)≤F.s at before
    have dpos : 0<d := by change _+1≤d at res;omega
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    by_contra fail
    have zero : originalThresholdCount ((componentBudget H F.m).entries F.m) 2=0 := by omega
    have fee := full_binary_unit_exterior_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn deg cap (by rw [swap];exact F.live)
      blue red ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [swap];exact data.2 small)
      small (by omega) (by change a+F.r+2*d≤F.t-μ;omega) ((highest_width_colour_swap _ _ _).le.trans width)
      res (trigger.2 blue) zero
    rw [row_energy_colour_swap F.m F.n] at fee;omega

#print axioms strict_full_binary_nonunit_remaining
end JSP452Audit.StarHost