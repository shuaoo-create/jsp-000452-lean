import RealMatchingAxisLossBudget
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

noncomputable def interiorInventory {X : Type*} [Finite X] (G : SimpleGraph X) (D : ℕ) : ℕ :=
  ∑q∈Finset.range (D-1),uniformEnvelope G (q+2)

/-- The first layers of the two actual envelope accounts are their
matching ranks. They keep the same deficit d on the original side. -/
theorem strict_two_interior_inventories {s t r D : ℕ} {X : Type u} [Finite X]
    (G : SimpleGraph X) (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (pos : 0<D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r) (strict : G.edgeSet.ncard<rowEnergy n m r) :
    let a := K.roots.ncard
    let μ := matchingEdges (G.induce K.core)
    let ρ := minimumExposure G D
    let B := G.induce K.rest
    let Z := eraseInternal G K.core
    (D-1)*(a+2*μ)+D*ρ+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest+
      interiorInventory B D+interiorInventory Z D<2*interiorArea n m r D+2*highestWidth n m r+2*d := by
  intro a μ ρ B Z
  have area := original_area_by_height hs ht n m hn hm pn pm top pos
  have fees := sum_actual_successor_fees G D K cap
  change (G.edgeSet.ncard-B.edgeSet.ncard)+(G.induce K.core).edgeSet.ncard=
    D*(a+2*μ)+D*ρ+(G.induce K.roots).edgeSet.ncard+crossCount G K.roots K.rest at fees
  have original := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+matchingEdges B at original
  have erased := whole_core_erasure_exact_rank G K
  change matchingEdges Z=a+matchingEdges B at erased
  have rest := erase_internal_edge_count G K.rest
  change G.edgeSet.ncard=_+B.edgeSet.ncard at rest
  have core := erase_internal_edge_count G K.core
  change G.edgeSet.ncard=Z.edgeSet.ncard+(G.induce K.core).edgeSet.ncard at core
  have budget (H : SimpleGraph X) := (envelope_reserve_account H (D-1)).1
  have b := (envelope_reserve_account B (D-1)).1
  change envelopeReserve B (D-1)+(matchingEdges B+interiorInventory B D)=B.edgeSet.ncard at b
  have z := budget Z
  change envelopeReserve Z (D-1)+(matchingEdges Z+interiorInventory Z D)=Z.edgeSet.ncard at z
  have prod : D*(a+2*μ)=(D-1)*(a+2*μ)+(a+2*μ) := by
    conv_lhs => rw [show D=D-1+1 by omega,Nat.add_mul,Nat.one_mul]
  omega

theorem strict_real_matched_loss_sum (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let D := diagonal F.n F.m (F.r+2)-1
    (F.t≤μ → (∑z∈matchingAxesFromThree F.n F.m F.r D,doubleEnvelopeLoss F.G K F.n F.m F.r (z+3))≤
      2*∑i,(F.n i-1)/2) ∧
    (F.s≤μ → (∑z∈matchingAxesFromThree F.m F.n F.r D,doubleEnvelopeLoss F.G K F.m F.n F.r (z+3))≤
      2*∑j,(F.m j-1)/2) := by
  intro μ D
  let d := F.rank-matchingEdges F.G
  obtain ⟨red,blue⟩ := strict_source_whole_list_alternatives F K
  have pos : 2≤d := (minimal_strict_source_deficit F paid).2.2
  constructor
  · intro embedded
    obtain ⟨half,_,_⟩ := blue.resolve_left (by change ¬μ+d+1≤F.t;omega)
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    exact sum_actual_matching_axes F.G K F.n F.m F.ht F.hn F.hm F.pn F.pm F.row
      (by change F.t+2*(∑j,(F.m j-1)/2)≤μ;omega)
  · intro embedded
    obtain ⟨half,_,_⟩ := red.resolve_left (by change ¬μ+d+1≤F.s;omega)
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    exact sum_actual_matching_axes F.G K F.m F.n F.hs F.hm F.hn F.pm F.pn (swap_positive_forcing_row F.G _ _ F.row)
      (by change F.s+2*(∑i,(F.n i-1)/2)≤μ;omega)

#print axioms strict_two_interior_inventories
#print axioms strict_real_matched_loss_sum
end JSP452Audit.StarHost
