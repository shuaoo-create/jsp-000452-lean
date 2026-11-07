import FiveBinarySingleExteriorPrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quintic_binary_nonunit_paid {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (five:D=5) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t 0) (row : ForcingRow G s t (padDemand n) (padDemand m) 0)
    (head : n ⟨0,hs⟩=D) (binary : m ⟨0,ht⟩=2) (top : diagonal n m (0+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t 0)
    (data : CompleteExteriorData G K n m 0 (rowCount s t 0) d)
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+2*(d+∑i,(n i-1)/2)≤t)
    (width : 1≤highestWidth n m 0 ∧ highestWidth n m 0≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d) (root : 3*minimumExposure G D+rootShortfall G K.roots D≤10)
    (trigger : FullMixedBoundary n m ht 0 D (matchingEdges (G.induce K.core)))
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2) :
    rowEnergy n m 0≤G.edgeSet.ncard := by
  subst D
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let Z := G.induce K.rest
  let k := matchingEdges Z
  let ρ := minimumExposure G 5
  let h := highestWidth n m 0
  let P := originalThresholdCount n 5
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let C := originalThresholdCount (W.entries n) 2
  let uf := uniformEnvelope Z
  let w := widthAt n m 0 2
  obtain ⟨j,y,yhi,eq,_,yp,over,_,_⟩ := trigger
  have bound := (original_threshold_prefix m hm y ⟨0,ht⟩).2 yp
  have ytwo : y=2 := by omega
  have jthree : j=3 := by omega
  rw [ytwo,jthree] at over
  have ppos : 0<P := (original_threshold_prefix n hn 5 ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 binary.ge
  have rect := actual_rectangle_le_column (r:=0) n m hn hm (a:=5) (b:=2) (h:=6) (by decide) ppos bpos
  have peak := width_at_actual_top (r:=0) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  have half := half_extra_pays_large_threshold n (show 3≤3 by decide)
  change P+B-1-0≤h at rect
  have guard : originalThresholdCount n 3+B≤t := by
    change ρ+1≤d at reserve;have wh : h≤ρ := width.2;omega
  obtain ⟨ph,p0,b0,winner,area⟩ := five_binary_zero_profile hs ht n m hn hm pn pm head binary live top over guard
  obtain ⟨_,fit,brow,_,_,_,_,_⟩ := data
  change W.loss≤μ at fit
  change μ<s at esc
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have size : s≤W.len+μ := by dsimp only [RemovalBudget.len];omega
  let wf := widthAt (W.entries n) m (0+a)
  have src (j:ℕ) (hi:0<j) : wf j≤uf j := widthAt_le_uniformEnvelope pos ht (W.entries n) m
    (W.entries_antitone n hn) hm (W.entries_positive n pn) pm _ _ j brow hi
  have pairs := exterior_binary_layer_bounds pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm (0+a) b0
  obtain ⟨wB,more⟩ := pairs
  obtain ⟨wR,wM⟩ := more nonunit
  change W.len+B-1-(0+a)≤wf 2 at wB
  change C+t-1-(0+a)≤wf 2 at wR
  change C+B-1-(0+a)≤wf 3 at wM
  obtain ⟨floor,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+C at floor
  have q2 := src 2 (by decide);have q3 := src 3 (by decide)
  have second : w≤a+μ+uf 2 := by
    change w=A+t-1 ∨ w=s+B-1 at winner
    rcases winner with x|y <;> omega
  have third : C+B≤uf 3+1+a := by omega
  have vol := nonunit_slot_volume G K n hn
  change 3*A≤3*C+2*μ+a+ρ at vol
  have cut := one_exterior_even_cut_bound G K n m hn hm pn pm ht row (by change t≤μ;change t+d≤μ+1 at inner;omega)
    binary 4 (by decide)
  have mass := half_extra_pays_large_threshold n (show 3≤4 by decide)
  have end4 : a+2*(d+originalThresholdCount n 4)≤t := by change a+2*(d+_)≤t at endpoint;omega
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at split
  have rk : rowCount s t 0=a+μ+k+d := by omega
  have fee := ordinary_region_original_edge_account G 5 cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots 5=10*(a+μ)+5*ρ+crossCount G K.roots K.rest+2*Z.edgeSet.ncard at fee
  have budget := (envelope_reserve_account Z 4).1
  change envelopeReserve Z 4+(k+(∑q∈Finset.range 4,uf (q+2)))=Z.edgeSet.ncard at budget
  have layers : (∑q∈Finset.range 4,uf (q+2))=uf 2+uf 3+uf 4+uf 5 := by simp [Finset.sum_range_succ]
  rw [layers] at budget
  exact five_binary_single_exterior_price s t a μ k d _ _ _ _ P A _ B C h ρ _ _ w (uf 2) (uf 3) (uf 4) (uf 5) rk fee width reserve inner
    end4 root (Nat.sub_le _ _) vol ph b0 p0 area second third cut (by omega)

#print axioms quintic_binary_nonunit_paid
end JSP452Audit.StarHost