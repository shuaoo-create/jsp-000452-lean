import OriginalRootEndpointWhenTheMatchingLossIsExact
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace NinePortRegion
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : NinePortRegion G)

noncomputable abbrev retainedEdges := eraseInternal G R.chosen
noncomputable abbrev jointPrice (j : ℕ) :=
  R.roots.ncard+2*R.totalCapacity+uniformEnvelope (G.induce R.outside) j+uniformEnvelope R.retainedEdges j

theorem joint_price_sum :
    (∑j∈Finset.range 8,R.jointPrice (j+2))=
      8*(R.roots.ncard+2*R.totalCapacity)+interiorInventory (G.induce R.outside) 9+interiorInventory R.retainedEdges 9 := by
  dsimp only [jointPrice]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorInventory]

theorem retained_edges_rank_floor (cap : ∀v,Nat.card (G.neighborSet v)≤9) :
    R.roots.ncard+R.outsideRank≤matchingEdges R.retainedEdges+R.rankAllowance := by
  have split := rank_of_two_edge_colours G R.retainedEdges (G\R.retainedEdges) (by
    intro x y e;by_cases kept:R.retainedEdges.Adj x y
    · exact Or.inl kept
    · exact Or.inr ⟨e,kept⟩)
  change matchingEdges G≤matchingEdges R.retainedEdges+matchingEdges (G\eraseInternal G R.chosen) at split
  rw [rank_of_internal_edges,(R.region_rank_edges cap).1] at split
  have actual := (R.root_deleted_rank_allowance cap).2
  omega

end NinePortRegion

theorem strict_nine_joint_matching_inventory (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) :
    let O := F.G.induce R.outside
    let Z := R.retainedEdges
    let d' := F.rank-matchingEdges F.G-R.rankAllowance
    (∑j∈Finset.range 8,R.jointPrice (j+2))+16+envelopeReserve O 8+envelopeReserve Z 8<
      2*interiorArea F.n F.m F.r 9+2*highestWidth F.n F.m F.r+2*d'+R.rootDebt+R.rankAllowance := by
  intro O Z d'
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq nine
  have eo := (R.root_deleted_edge_account cap).1
  have ez := erase_internal_edge_count F.G R.chosen
  rw [(R.region_rank_edges cap).2.1] at ez
  change F.G.edgeSet.ncard=Z.edgeSet.ncard+(9*R.totalCapacity+8) at ez
  have nr := (strict_nine_root_deleted_row F paid nine R).2.1
  change F.s+F.t-1-(F.r+R.roots.ncard)=R.totalCapacity+R.outsideRank+d' at nr
  have balance : F.rank=R.roots.ncard+R.totalCapacity+R.outsideRank+d' := by
    change F.s+F.t-1-F.r=_;have pos := (strict_nine_root_deleted_row F paid nine R).1;omega
  have rz := R.retained_edges_rank_floor cap
  change R.roots.ncard+R.outsideRank≤matchingEdges Z+R.rankAllowance at rz
  have invO := (envelope_reserve_account O 8).1
  have invZ := (envelope_reserve_account Z 8).1
  change envelopeReserve O 8+(R.outsideRank+interiorInventory O 9)=O.edgeSet.ncard at invO
  change envelopeReserve Z 8+(matchingEdges Z+interiorInventory Z 9)=Z.edgeSet.ncard at invZ
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=9) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 9+highestWidth F.n F.m F.r at area
  have strict := F.strict
  rw [R.joint_price_sum]
  change 8*(R.roots.ncard+2*R.totalCapacity)+interiorInventory O 9+interiorInventory Z 9+
    16+envelopeReserve O 8+envelopeReserve Z 8<_
  change F.G.edgeSet.ncard+R.rootDebt=O.edgeSet.ncard+9*(R.roots.ncard+R.totalCapacity)+8 at eo
  omega

theorem strict_nine_joint_residual_area (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) (long : R.totalCapacity<F.s) :
    let a := R.roots.ncard
    let P := R.totalCapacity
    let W := componentBudget (F.G.induce R.chosen) F.n
    let J := commonErasedDemand F.n W a P
    let delta := P-W.loss
    8*(a+2*P)+interiorArea (W.entries F.n) F.m (F.r+a) 9+interiorArea J F.m F.r 9+16+2*delta<
      2*interiorArea F.n F.m F.r 9+2*highestWidth F.n F.m F.r+R.rootDebt := by
  intro a P W J delta
  obtain ⟨alive,_,fit,rankB,rankZ,_,_,_,_,paidB,paidZ⟩ := nine_long_side_actual_source_prices F paid nine R long
  change 0<W.len at alive
  change W.loss≤P at fit
  let LB := interiorArea (W.entries F.n) F.m (F.r+a) 9
  let LZ := interiorArea J F.m F.r 9
  have cb := interior_area_lower (r:=F.r+a) (D:=9) alive F.ht (W.entries F.n) F.m
    (W.entries_positive F.n F.pn) F.pm (by decide : 0<9)
  have cz := interior_area_lower (r:=F.r) (D:=9) alive F.ht J F.m
    (common_erased_positive F.n W a P) F.pm (by decide : 0<9)
  have num : W.len+W.loss=F.s := by change F.s-W.loss+W.loss=F.s;omega
  change rowCount W.len F.t (F.r+a)=R.outsideRank+(F.rank-matchingEdges F.G-R.rankAllowance)+(P-W.loss) at rankB
  change rowCount W.len F.t F.r=a+R.outsideRank+(F.rank-matchingEdges F.G-R.rankAllowance)+(P-W.loss) at rankZ
  have rank : rowCount W.len F.t (F.r+a)+rowCount W.len F.t F.r+2*W.loss+a=2*F.rank := by
    have positive := (strict_nine_root_deleted_row F paid nine R).1
    change 2≤F.rank-matchingEdges F.G-R.rankAllowance at positive
    dsimp only [StrictFamily.rank,rowCount] at rankB rankZ positive ⊢;omega
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=9) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 9+highestWidth F.n F.m F.r at area
  change rowEnergy (W.entries F.n) F.m (F.r+a)+9*(a+P)+8≤F.G.edgeSet.ncard+R.rootDebt at paidB
  change rowEnergy J F.m F.r+9*P+8≤F.G.edgeSet.ncard at paidZ
  have strict := F.strict
  dsimp only [delta]
  omega

#print axioms NinePortRegion.joint_price_sum
#print axioms NinePortRegion.retained_edges_rank_floor
#print axioms strict_nine_joint_matching_inventory
#print axioms strict_nine_joint_residual_area
end JSP452Audit.StarHost
