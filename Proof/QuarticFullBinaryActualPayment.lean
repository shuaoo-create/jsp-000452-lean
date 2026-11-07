import QuarticBinaryEdgePayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quartic_full_binary_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (four:D=4) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (binary : m ⟨0,ht⟩=2) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (root : 4*minimumExposure G D+rootShortfall G K.roots D≤2*highestWidth n m r+10) (lim : minimumExposure G D≤5)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core))) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let S := s-μ
  let W := componentBudget H n
  let Z := G.induce K.rest
  let ρ := minimumExposure G 4
  let h := highestWidth n m r
  let P := originalThresholdCount n 4
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let F₃ := originalThresholdCount n 3
  let c := originalThresholdCount (W.entries n) 2
  let NB := rowCount W.len t (r+a)
  obtain ⟨j,y,yhi,eq,_,yp,over,_,_⟩ := trigger
  have bound := (original_threshold_prefix m hm y ⟨0,ht⟩).2 yp
  have ytwo : y=2 := by omega
  have jthree : j=3 := by omega
  rw [ytwo,jthree] at over
  have full := (original_threshold_prefix n hn 4 ⟨0,hs⟩).1 head.ge
  have red := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 binary.ge
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=4) (b:=2) (h:=5) (by decide) full red
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  have half := half_extra_pays_large_threshold n (show 3≤3 by decide)
  have guard : F₃+B≤t := by
    change P+B-1-r≤h at rect;change 0<P at full
    change F₃≤_ at half
    have hw : h≤ρ := width.2
    omega
  obtain ⟨ph,p0,b0,winner,area⟩ := quartic_binary_profile hs ht n m hn hm pn pm head binary live top over guard
  obtain ⟨lo,fit,row,bsize,_,_,_,cheap⟩ := data
  change W.loss≤μ at fit
  change 1≤W.loss at lo
  change μ<s at esc
  have len : s=S+μ := by dsimp [S];omega
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have size : S≤W.len := by dsimp only [S,RemovalBudget.len];omega
  let k := matchingEdges Z
  change NB=k+d+(μ-W.loss) at bsize
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at split
  have boundN : rowCount s t r≤NB+(a+μ) := by omega
  have fee := ordinary_region_original_edge_account G 4 cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots 4=8*(a+μ)+4*ρ+crossCount G K.roots K.rest+2*Z.edgeSet.ncard at fee
  have zs : rootShortfall G K.roots 4≤4*a := Nat.sub_le _ _
  have credit := four_root_lower_charge a h ρ _ (crossCount G K.roots K.rest) width.1 width.2 root zs
  have layer := row_area_three_layers (r:=r+a) pos ht (W.entries n) m (W.entries_positive n pn) pm
  have pairs := exterior_binary_layer_bounds pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm (r+a) b0
  change rowEnergy (W.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
  have paid := layer.trans cheap
  obtain ⟨nL,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+c at nL
  by_cases nonunit : 0<c
  · obtain ⟨bfee,more⟩ := pairs
    obtain ⟨rfee,mfee⟩ := more nonunit
    exact four_binary_retained_pays s t r a μ S _ NB _ _ _ P A B c h ρ _ _ d _ _ _ len boundN (by omega) reserve width.2
      inner fee credit ph b0 area winner (by omega) rfee (by omega) mfee paid
  · have none : c=0 := by omega
    have few : A≤μ := by omega
    have volume := unit_residual_nonunit_volume G K n hn esc none
    change μ≤3*(μ-A)+a+ρ at volume
    have slots : 3*A≤2*μ+a+ρ := by omega
    have blue := pairs.1
    have order : P≤F₃ := threshold_anti_height n (show 3≤4 by decide)
    exact four_binary_unit_pays s t r a μ S _ NB _ _ _ P A F₃ B h ρ _ _ d _ len boundN reserve width.2 lim inner
      outer (by omega) b0 fee credit ph p0 order area winner few slots over (by omega)

#print axioms quartic_full_binary_paid
end JSP452Audit.StarHost
