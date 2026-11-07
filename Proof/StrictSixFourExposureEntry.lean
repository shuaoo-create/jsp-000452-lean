import ActualSixPositiveWeightCeiling
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_four_exposure_entry (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (K:DegreeRegion F.G 6) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 6).ncard
    let ρ := minimumExposure F.G 6
    1≤h ∧ h≤c ∧ c≤ρ ∧ ρ≤4 ∧
      (ρ=4 → h=4 ∧ c=4 ∧ edgeSurplus (F.G.induce K.positiveCore) 6=12 ∧
        rootShortfall F.G K.roots 6=0 ∧ (F.G.induce K.roots).edgeSet.ncard=0 ∧ crossCount F.G K.roots K.rest=0) := by
  intro h c ρ
  obtain ⟨lo,first,second,_,_⟩ := strict_six_real_component_bounds F paid six
  change 1≤h at lo
  change h≤c at first
  change c≤ρ at second
  have degree := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:F.X) : Nat.card (F.G.neighborSet v)≤6 := (degree v).trans_eq six
  have exactCost := K.weight_identity cap
  have pos := positivePieces_dominate F.G K.barrier K.pieces 6
  change edgeSurplus (F.G.induce K.core) 6≤edgeSurplus (F.G.induce K.positiveCore) 6 at pos
  have ceiling := strict_six_positive_weight_ceiling F paid six K
  change edgeSurplus (F.G.induce K.positiveCore) 6≤(h:ℤ)+8 at ceiling
  change 2*edgeSurplus (F.G.induce K.core) 6=6*(ρ:ℤ)+
    (rootShortfall F.G K.roots 6:ℤ)+2*((F.G.induce K.roots).edgeSet.ncard:ℤ)+(crossCount F.G K.roots K.rest:ℤ) at exactCost
  refine ⟨lo,first,second,by omega,?_⟩
  intro four
  refine ⟨by omega,by omega,by omega,by omega,by omega,by omega⟩

#print axioms strict_six_four_exposure_entry
end JSP452Audit.StarHost
