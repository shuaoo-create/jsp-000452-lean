import ActualWeightSuccessor
import FiveDegreeSelectorCeiling
namespace JSP452Audit.StarHost
universe u

/-- The exact surplus of this particular positive core is bounded at a
strict original row by its actual top width and the price of omitted pieces. -/
theorem strict_source_positive_weight_cap (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    edgeSurplus (F.G.induce K.positiveCore) D+1 ≤ (highestWidth F.n F.m F.r:ℤ)+
      ((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) := by
  intro D
  have degree : 3≤D := strict_source_degree_at_least_three F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have hp := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).1
  by_cases heavy : ((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)<edgeSurplus (F.G.induce K.positiveCore) D
  · obtain ⟨U,T,progress,gain,next,saving⟩ := actual_weight_successor F.G D K cap
      (padDemand F.n) (padDemand F.m) (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
      (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row heavy
    have price := smaller_source_price F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G _
      F.r _ D F.rank paid F.live le_rfl progress top.le next _ saving
    rw [←top,width_at_actual_top F.hs F.ht F.n F.m F.hn F.hm] at price
    have strict : (F.G.edgeSet.ncard:ℤ)<rowEnergy F.n F.m F.r := by exact_mod_cast F.strict
    omega
  omega

/-- The same bound includes the root slack and both types of edges incident
with roots. It holds for every ordinary region of the given original source. -/
theorem strict_source_region_root_budget (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    D*minimumExposure F.G D+rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest+2 ≤ 2*highestWidth F.n F.m F.r + 2*(D/2)*(D/2+1) := by
  intro D
  have ceil := strict_source_positive_weight_cap F paid K
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have total := K.weight_identity cap
  have raised := positivePieces_dominate F.G K.barrier K.pieces D
  change edgeSurplus (F.G.induce K.core) D≤edgeSurplus (F.G.induce K.positiveCore) D at raised
  change edgeSurplus (F.G.induce K.positiveCore) D+1≤(highestWidth F.n F.m F.r:ℤ)+((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) at ceil
  change 2*edgeSurplus (F.G.induce K.core) D=(D:ℤ)*(minimumExposure F.G D:ℤ)+
    (rootShortfall F.G K.roots D:ℤ)+2*((F.G.induce K.roots).edgeSet.ncard:ℤ)+(crossCount F.G K.roots K.rest:ℤ) at total
  have right : 2*(D/2)*(D/2+1)=2*((D/2)*(D/2+1)) := Nat.mul_assoc _ _ _
  rw [right]
  have z : (D:ℤ)*(minimumExposure F.G D:ℤ)+(rootShortfall F.G K.roots D:ℤ)+
      2*((F.G.induce K.roots).edgeSet.ncard:ℤ)+(crossCount F.G K.roots K.rest:ℤ)+2 ≤
      2*(highestWidth F.n F.m F.r:ℤ)+2*(((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1)) := by omega
  exact_mod_cast z

#print axioms strict_source_positive_weight_cap
#print axioms strict_source_region_root_budget
end JSP452Audit.StarHost
