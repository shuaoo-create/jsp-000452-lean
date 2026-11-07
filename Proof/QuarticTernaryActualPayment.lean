import QuarticTernaryPriceArithmetic
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quartic_full_ternary_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (four:D=4) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (blue : m ⟨0,ht⟩=3) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (inner : t+d≤matchingEdges (G.induce K.core)+1)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (root : 4*minimumExposure G D+rootShortfall G K.roots D≤2*highestWidth n m r+10)
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
  let F₃ := originalThresholdCount n 3
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let Q := originalThresholdCount m 3
  let c := originalThresholdCount (W.entries n) 2
  let NB := rowCount W.len t (r+a)
  have full : 0<P := (original_threshold_prefix n hn 4 ⟨0,hs⟩).1 head.ge
  have qpos : 0<Q := (original_threshold_prefix m hm 3 ⟨0,ht⟩).1 blue.ge
  have bpos : 0<B := qpos.trans_le (threshold_anti_height m (show 2≤3 by decide))
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=4) (b:=2) (h:=5) (by decide) full bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  have gB : B≤r+ρ := by change P+B-1-r≤h at rect;have wh : h≤ρ := width.2;omega
  have half := half_extra_pays_large_threshold n (show 3≤3 by decide)
  have guard : F₃+B≤t := by change F₃≤_ at half;change ρ+1≤d at reserve;omega
  obtain ⟨p0,q0,qLim,pLim,fLim,w2,w3,w4,area⟩ := quartic_ternary_profile n m hs ht hn hm pn pm head blue live top guard
  obtain ⟨lo,fit,_,bsize,_,_,_,cheap⟩ := data
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
  have credit := four_root_lower_charge a h ρ _ (crossCount G K.roots K.rest) width.1 width.2 root
    (show rootShortfall G K.roots 4≤4*a from Nat.sub_le _ _)
  have layer := interior_area_lower (r:=r+a) (D:=4) pos ht (W.entries n) m (W.entries_positive n pn) pm (by decide)
  change rowEnergy (W.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
  have paid : NB+widthAt (W.entries n) m (r+a) 2+widthAt (W.entries n) m (r+a) 3+widthAt (W.entries n) m (r+a) 4
      ≤Z.edgeSet.ncard := by simpa [NB,interiorArea,Finset.sum_range_succ,Nat.add_assoc] using layer.trans cheap
  have pairs := exterior_binary_layer_bounds pos ht (W.entries n) m (W.entries_antitone n hn) hm (W.entries_positive n pn) pm (r+a) bpos
  have one := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have t3 := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
    (a:=1) (b:=3) (h:=3) (by decide) (one.symm ▸ pos) qpos
  rw [one] at t3
  obtain ⟨nL,_,_,_⟩ := common_threshold_floors n hn pn W a μ 2 fit
  change A≤W.loss+c at nL
  by_cases nonunit : 0<c
  · have slot := original_two_threshold_slot_guard G K n hn (by decide : 3≤4) cap
    change 4*ρ+rootShortfall G K.roots 4+4*A≤4*(μ+c) at slot
    have margin := quartic_slot_root_margin μ A c h ρ _ (crossCount G K.roots K.rest) width.1 width.2 root slot
    obtain ⟨bfee,more⟩ := pairs
    obtain ⟨rfee,mfee⟩ := more nonunit
    have t4 := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
      (a:=2) (b:=3) (h:=4) (by decide) nonunit qpos
    exact quartic_ternary_retained_pays s t r a μ S _ NB _ _ _ P F₃ A B Q c h ρ _ _ d _ _ _ _ _ _ len boundN (by omega)
      reserve width.2 inner fee credit margin pLim fLim area w2 w3 w4 (by omega) rfee (by omega) mfee (by omega) t4 paid
  · have none : c=0 := by omega
    have few : A≤μ := by omega
    have volume := unit_residual_nonunit_volume G K n hn esc none
    change μ≤3*(μ-A)+a+ρ at volume
    have slots : 3*A≤2*μ+a+ρ := by omega
    obtain ⟨j,y,_,_,_,_,over,_,last⟩ := trigger
    have eb := last few
    have y3 : y=3 := eb.1.trans blue
    have j4 : j=4 := by omega
    rw [y3,j4] at over
    have bfee := pairs.1
    exact quartic_ternary_unit_pays s t r a μ S _ NB _ _ _ P F₃ A B Q h ρ _ _ d _ _ _ len boundN reserve width.2
      inner outer (by omega) fee credit fLim gB bpos qpos qLim p0 area w2 w3 w4 few slots over (by omega)

#print axioms quartic_full_ternary_paid
end JSP452Audit.StarHost
