import ClosedRegularRegionOddParity
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_six_component_exposure_classes (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) :
    let c := (oddRegularComponents F.G 6).ncard
    let ρ := minimumExposure F.G 6
    (c=1 → ρ≤2) ∧ (2≤c → c=ρ) := by
  intro c ρ
  let U := {v:F.X|F.G.connectedComponentMk v∈oddRegularComponents F.G 6}
  have closed (v:F.X) (hv:v∈U) (w:F.X) (edge:F.G.Adj v w) : w∈U := by
    change F.G.connectedComponentMk w∈oddRegularComponents F.G 6
    rwa [←ConnectedComponent.sound edge.reachable]
  have full (v:F.X) (hv:v∈U) : Nat.card (F.G.neighborSet v)=6 := hv.2 v rfl
  obtain ⟨K,sub⟩ := ordinary_region_covers_closed_full_set F.G 6 U closed full
  let h := highestWidth F.n F.m F.r
  have hc := strict_six_four_exposure_entry F paid six K
  change 1≤h ∧ h≤c ∧ c≤ρ ∧ ρ≤4 ∧ _ at hc
  obtain ⟨_,hc,cr,top,atFour⟩ := hc
  have orig := (minimal_rank_exact_source F paid).2.2.2.1
  have cap (v:F.X) := (orig v).trans_eq six
  have exactCost := K.weight_identity cap
  change 2*edgeSurplus (F.G.induce K.core) 6=6*(ρ:ℤ)+
    (rootShortfall F.G K.roots 6:ℤ)+2*((F.G.induce K.roots).edgeSet.ncard:ℤ)+(crossCount F.G K.roots K.rest:ℤ) at exactCost
  have pos := positivePieces_dominate F.G K.barrier K.pieces 6
  change edgeSurplus (F.G.induce K.core) 6≤edgeSurplus (F.G.induce K.positiveCore) 6 at pos
  have bound := strict_six_saturated_weight_ceiling F paid six K
  change edgeSurplus (F.G.induce K.positiveCore) 6+1≤(h:ℤ)+6+(c:ℤ) at bound
  constructor
  · intro one;omega
  · intro multiple
    by_contra neq
    have uneven : c=2 ∧ ρ=3 := by
      by_cases last : ρ=4
      · have fourth := (atFour last).2.1
        change c=4 at fourth
        omega
      · omega
    have root : rootShortfall F.G K.roots 6=0 := by omega
    have boundary : crossCount F.G K.roots K.rest=0 := by omega
    obtain ⟨sealed,regular,order⟩ := zero_loss_full_closed_region K cap root boundary
    obtain ⟨k,parity⟩ := regular_region_parity F.G 6 (K.core∪K.roots) sealed regular
      (fun v hv => sub (show v∈U from hv))
    change (K.core∪K.roots).ncard=2*k+c at parity
    change (K.core∪K.roots).ncard=2*(matchingEdges (F.G.induce K.core)+K.roots.ncard)+ρ at order
    clear * - uneven parity order
    omega

#print axioms strict_six_component_exposure_classes
end JSP452Audit.StarHost
