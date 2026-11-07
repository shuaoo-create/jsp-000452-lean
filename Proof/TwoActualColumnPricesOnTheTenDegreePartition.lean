import TwoSmallerRowsOnTheOriginalTenDegreeHost
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

namespace TenBlockPartition
variable {X : Type u} [Finite X] {G : SimpleGraph X} (R : TenBlockPartition G)
noncomputable abbrev retainedEdges := eraseInternal G R.core
noncomputable abbrev jointPrice (j : ℕ) :=
  R.roots.ncard+2*R.capacity+uniformEnvelope (G.induce R.rest) j+uniformEnvelope R.retainedEdges j

theorem joint_price_sum :
    (∑j∈Finset.range 9,R.jointPrice (j+2))=
      9*(R.roots.ncard+2*R.capacity)+interiorInventory (G.induce R.rest) 10+interiorInventory R.retainedEdges 10 := by
  dsimp only [jointPrice]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorInventory]

noncomputable abbrev basicPrice {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r j : ℕ) :=
  let W := componentBudget (G.induce R.core) n
  R.roots.ncard+2*R.capacity+widthAt (W.entries n) m (r+R.roots.ncard) j+
    widthAt (commonErasedDemand n W R.roots.ncard R.capacity) m r j

theorem basic_price_sum {s t : ℕ} (n : Fin s→ℕ) (m : Fin t→ℕ) (r : ℕ) :
    let W := componentBudget (G.induce R.core) n
    (∑j∈Finset.range 9,R.basicPrice n m r (j+2))=9*(R.roots.ncard+2*R.capacity)+
      interiorArea (W.entries n) m (r+R.roots.ncard) 10+
      interiorArea (commonErasedDemand n W R.roots.ncard R.capacity) m r 10 := by
  intro W
  dsimp only [basicPrice]
  rw [Finset.sum_add_distrib,Finset.sum_add_distrib]
  simp [interiorArea,W]

end TenBlockPartition

theorem ten_joint_envelope_account (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (ten : diagonal F.n F.m (F.r+2)-1=10) (R : TenBlockPartition F.G) :
    let O := F.G.induce R.rest
    let Z := R.retainedEdges
    let d := F.rank-matchingEdges F.G
    (∑j∈Finset.range 9,R.jointPrice (j+2))+10*R.eta+(F.G.induce R.roots).edgeSet.ncard+
      crossCount F.G R.roots R.rest+envelopeReserve O 9+envelopeReserve Z 9<
      2*interiorArea F.n F.m F.r 10+2*highestWidth F.n F.m F.r+2*d+R.epsilon := by
  intro O Z d
  have cap (v) := ((minimal_rank_exact_source F paid).2.2.2.1 v).trans_eq ten
  have fee := (R.edge_fees cap).2.2.2.1
  change 2*F.G.edgeSet.ncard+R.epsilon=O.edgeSet.ncard+Z.edgeSet.ncard+10*(R.roots.ncard+2*R.capacity)+
    10*R.eta+(F.G.induce R.roots).edgeSet.ncard+crossCount F.G R.roots R.rest at fee
  have rz := R.erased_core_rank
  change matchingEdges Z=R.roots.ncard+R.outsideRank at rz
  have rank := R.rank
  change matchingEdges F.G=R.roots.ncard+R.capacity+R.outsideRank at rank
  have pos := (ten_physical_root_deleted_row F paid R).1
  have balance : F.rank=R.roots.ncard+R.capacity+R.outsideRank+d := by dsimp only [d];omega
  have invO := (envelope_reserve_account O 9).1
  have invZ := (envelope_reserve_account Z 9).1
  change envelopeReserve O 9+(R.outsideRank+interiorInventory O 10)=O.edgeSet.ncard at invO
  change envelopeReserve Z 9+(matchingEdges Z+interiorInventory Z 10)=Z.edgeSet.ncard at invZ
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=10) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 10+highestWidth F.n F.m F.r at area
  have strict := F.strict
  rw [R.joint_price_sum]
  change 9*(R.roots.ncard+2*R.capacity)+interiorInventory O 10+interiorInventory Z 10+_+_+_+_+_<_
  omega

#print axioms TenBlockPartition.joint_price_sum
#print axioms TenBlockPartition.basic_price_sum
#print axioms ten_joint_envelope_account
end JSP452Audit.StarHost
