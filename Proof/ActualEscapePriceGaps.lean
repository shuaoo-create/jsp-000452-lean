import StrictRegionEscapeClassification
import OriginalRegionEdgeAccount
namespace JSP452Audit.StarHost
universe u

/-- At an escaping list, the original row area exceeds both actual
successor prices, including the original edges removed to reach each
successor. No two costs are added when they use overlapping edges. -/
def EscapePriceGap {X : Type u} [Finite X] (G : SimpleGraph X) {D : ℕ}
    (K : DegreeRegion G D) {s t : ℕ} (n : Fin s → ℕ) (m : Fin t → ℕ) (r E : ℕ) : Prop :=
  let B := G.induce K.rest
  let e := G.edgeSet.ncard
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let c := (G.induce K.core).edgeSet.ncard
  let p := rowEnergy (remainingDemand n μ) m r
  let q := rowEnergy (remainingDemand n μ) m (r+a)
  p ≤ (eraseInternal G K.core).edgeSet.ncard ∧ q ≤ B.edgeSet.ncard ∧
    max (p+c) (q+(e-B.edgeSet.ncard)) < E ∧
    2*(D*(a+μ))+D*minimumExposure G D+crossCount G K.roots K.rest+2*q <
      2*E+rootShortfall G K.roots D

theorem strict_same_region_escape_prices (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let E := rowEnergy F.n F.m F.r
    (μ<F.s → EscapePriceGap F.G K F.n F.m F.r E) ∧
    (μ<F.t → EscapePriceGap F.G K F.m F.n F.r E) := by
  intro μ E
  have erased := strict_source_paid_erased_core_successors F paid K
  have actual := strict_exterior_whole_tail_prices F paid K
  have strict := F.strict
  change F.G.edgeSet.ncard < E at strict
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have account := ordinary_region_original_edge_account F.G _ cap K
  rw [Nat.mul_assoc] at account
  have sub := erase_internal_edge_count F.G K.rest
  constructor
  · intro red
    obtain ⟨_,_,_,_,_,p,c⟩ := erased.2.2.2 red
    have q := (actual.1 red).2.2.1
    dsimp only [EscapePriceGap]
    refine ⟨p,q, max_lt_iff.mpr ⟨lt_of_le_of_lt c strict, ?_⟩, ?_⟩ <;> omega
  · intro blue
    obtain ⟨_,_,_,_,_,p,c⟩ := erased.2.2.1 blue
    have q := (actual.2 blue).2.2.1
    rw [←row_energy_colour_swap (remainingDemand F.m μ) F.n] at p c q
    dsimp only [μ] at p c q
    dsimp only [EscapePriceGap]
    refine ⟨p,q, max_lt_iff.mpr ⟨lt_of_le_of_lt c strict, ?_⟩, ?_⟩ <;> omega

#print axioms strict_same_region_escape_prices
end JSP452Audit.StarHost
