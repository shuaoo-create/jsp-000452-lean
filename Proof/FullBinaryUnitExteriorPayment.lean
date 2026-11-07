import BinaryUnitNaturalPrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_binary_unit_exterior_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (deg : 5≤D) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (binary : m ⟨0,ht⟩=2) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s)
    (before : r<t) (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : highestWidth n m r≤minimumExposure G D) (reserve : minimumExposure G D+1≤d)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let S := s-μ
  let W := componentBudget H n
  let Z := G.induce K.rest
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let NB := rowCount W.len t (r+a)
  obtain ⟨j,y,yhi,eq,_,yp,over,_,_⟩ := trigger
  have bound := (original_threshold_prefix m hm y ⟨0,ht⟩).2 yp
  have ytwo : y=2 := by omega
  have jthree : j=3 := by omega
  rw [ytwo,jthree] at over
  obtain ⟨ph,p0,b0,winner,area⟩ := full_binary_general_profile hs ht n m hn hm pn pm (by omega) head binary live top over
  obtain ⟨lo,fit,_,bsize,_,_,_,cheap⟩ := data
  change W.loss≤μ at fit
  change μ<s at esc
  have len : s=S+μ := by dsimp [S];omega
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have size : S≤W.len := by dsimp only [S,RemovalBudget.len];omega
  let k := matchingEdges Z
  change NB=k+d+(μ-W.loss) at bsize
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at split
  have boundN : rowCount s t r≤NB+(a+μ) := by omega
  have layer := row_area_three_layers (r:=r+a) pos ht (W.entries n) m (W.entries_positive n pn) pm
  have pairs := exterior_binary_layer_bounds pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm (r+a) b0
  change rowEnergy (W.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
  have paid := layer.trans cheap
  have blue := pairs.1
  change W.len+B-1-(r+a)≤widthAt (W.entries n) m (r+a) 2 at blue
  have edgeB : NB+(S+B-1-(r+a))≤Z.edgeSet.ncard := by change NB+_+_≤Z.edgeSet.ncard at paid;omega
  have slot := original_two_threshold_slot_guard G K n hn (by omega) cap
  change D*ρ+rootShortfall G K.roots D+D*A≤D*(μ+originalThresholdCount (W.entries n) 2) at slot
  change originalThresholdCount (W.entries n) 2=0 at unit
  rw [unit,Nat.add_zero] at slot
  change D*ρ+rootShortfall G K.roots D+D*A≤D*μ at slot
  obtain ⟨floor,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change originalThresholdCount (W.entries n) 2=0 at unit
  change A≤W.loss+originalThresholdCount (W.entries n) 2 at floor
  rw [unit,Nat.add_zero] at floor
  have volume := unit_residual_nonunit_volume G K n hn esc unit
  change μ≤3*(μ-A)+a+ρ at volume
  have slots : 3*A≤2*μ+a+ρ := by omega
  exact binary_unit_general_payment s t r D a μ S _ NB _ _ _ _ A _ B h ρ _ _ d _ deg len boundN reserve width
    outer before p0 (ordinary_region_original_edge_account G D cap K) slot (Nat.sub_le _ _) slots ph over area winner edgeB

#print axioms full_binary_unit_exterior_paid
end JSP452Audit.StarHost