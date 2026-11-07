import QuinticRetainedEnergyPrices
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quintic_full_retained_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (five:D=5) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (row : ForcingRow G s t (padDemand n) (padDemand m) r)
    (head : n ⟨0,hs⟩=D) (heads : m ⟨0,ht⟩=3 ∨ m ⟨0,ht⟩=4) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (inner : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d) (root : 3*minimumExposure G D+rootShortfall G K.roots D≤10)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (nonunit : 0<originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2) : rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let M := a+μ
  let L := componentBudget H n
  let Z := G.induce K.rest
  let k := matchingEdges Z
  let ρ := minimumExposure G 5
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let c := originalThresholdCount (L.entries n) 2
  let V := μ+c-A
  let C := widthAt n m r
  let U := widthAt (L.entries n) m (r+a)
  let uf := uniformEnvelope Z
  let NB := rowCount L.len t (r+a)
  change ρ+1≤d at reserve
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at inner
  change a+r+2*(d+∑i,(n i-1)/2)≤t at endpoint
  have wh : h≤ρ := width.2
  have p := (original_threshold_prefix n hn 5 ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by rcases heads with b|b <;> omega)
  have apos : 0<A := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=5) (b:=2) (h:=6) (by decide) p bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change originalThresholdCount n 5+B-1-r≤h at rect
  have guard : (∑i,(n i-1)/2)+B≤t := by omega
  obtain ⟨_,fit,brow,bsize,_,_,_,cheap⟩ := data
  change L.loss≤μ at fit
  change μ<s at esc
  change NB=k+d+(μ-L.loss) at bsize
  have pos : 0<L.len := by dsimp only [RemovalBudget.len];omega
  have len : s≤L.len+μ := by dsimp only [RemovalBudget.len];omega
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at split
  have rn : rowCount s t r=a+μ+k+d := by omega
  have rk : rowCount s t r≤NB+a+μ := by omega
  have fee := ordinary_region_original_edge_account G 5 cap K
  change 2*G.edgeSet.ncard+rootShortfall G K.roots 5=10*(a+μ)+5*ρ+crossCount G K.roots K.rest+2*Z.edgeSet.ncard at fee
  obtain ⟨floor,_,_,_⟩ := common_threshold_floors n hn pn L a μ 2 fit
  change A≤L.loss+c at floor
  have fitA : A≤μ+c := by omega
  have balance : V+A=μ+c := by dsimp [V];omega
  obtain ⟨two,each,j,jlo,jhi,jb,mix⟩ := full_retained_exterior_layers hs ht pos n m (L.entries n) hn hm (L.entries_antitone n hn)
    pn pm (L.entries_positive n pn) (by omega) live top (by decide) fitA len nonunit bpos apos guard trigger
  change C 2≤M+U 2 at two
  change ∀z,3≤z → z≤5 → C z≤originalThresholdCount n z+t-1-r ∨ C z≤M+U z at each
  change C j+V≤M+U j at mix
  have area := original_area_by_height hs ht n m hn hm pn pm top (by decide)
  have sumC : interiorArea n m r 5=C 2+C 3+C 4+C 5 := by simp [interiorArea,C,Finset.sum_range_succ]
  rw [sumC] at area
  have orig : rowEnergy n m r≤rowCount s t r+C 2+C 3+C 4+C 5+h := by change _=_+_+h at area;omega
  have bounded (x z:ℕ) (lo:3≤z) (hi:z≤5) (xz:x≤z) (px : originalThresholdCount n x≤r+h) : C z≤M+U z := by
    rcases each z lo hi with red|paid
    · have mono := threshold_anti_height n xz
      change C z≤(a+μ)+U z;omega
    · exact paid
  rcases heads with ternary|four
  · have cap4 := quintic_red_prefix_at_peak hs ht n m hn hm head ternary top (by decide : 4+3=7) (by decide)
    have at4 := bounded 4 4 (by decide) (by decide) le_rfl cap4
    have top5 := quintic_ternary_last_axis hs ht n m hn hm pn pm head ternary top live guard
    change C 5≤t-1 at top5
    have end5 : C 5+a+d≤a+μ := by omega
    have real (q:ℕ) (yes:0<q) : U q≤uf q := widthAt_le_uniformEnvelope pos ht (L.entries n) m (L.entries_antitone n hn)
      hm (L.entries_positive n pn) pm _ _ q brow yes
    have u2 := real 2 (by decide);have u3 := real 3 (by decide);have u4 := real 4 (by decide)
    have three : 2*C 3≤2*(M+uf 3)+originalThresholdCount n 3 := by
      rcases each 3 (by decide) (by decide) with axis|paid
      · have cut := one_exterior_offset_cut G K n m hn hm pn pm ht row (by change t+_≤μ;omega) 3 (by decide)
        change 2*(originalThresholdCount n 3+t-1-r)≤2*(M+uf 3)+originalThresholdCount n 3 at cut
        omega
      · omega
    have gain : C 3+V≤M+uf 3 ∨ C 4+V≤M+uf 4 := by
      rw [ternary] at jb
      rcases (show j=3 ∨ j=4 by omega) with z|z <;> rw [z] at mix <;> omega
    have middle := quintic_ternary_middle M V _ (C 3) (C 4) (uf 3) (uf 4) (by omega) three gain
    have budget := (envelope_reserve_account Z 4).1
    change envelopeReserve Z 4+(k+(∑q∈Finset.range 4,uf (q+2)))=Z.edgeSet.ncard at budget
    have layers : (∑q∈Finset.range 4,uf (q+2))=uf 2+uf 3+uf 4+uf 5 := by simp [Finset.sum_range_succ]
    rw [layers] at budget
    have volume := nonunit_slot_volume G K n hn
    change 3*A≤3*c+2*μ+a+ρ at volume
    have half := half_extra_pays_large_threshold n (show 3≤3 by decide)
    exact quintic_ternary_energy a μ _ k d _ _ _ h ρ _ _ V _ t (C 2) (C 3) (C 4) (C 5)
      (uf 2) (uf 3) (uf 4) (uf 5) rn fee width reserve (by omega) (by omega) root (Nat.sub_le _ _) (by omega)
      orig (by omega) (by change C 2≤M+uf 2;omega) middle end5
  · have cap3 := quintic_red_prefix_at_peak hs ht n m hn hm head four top (by decide : 3+4=7) (by decide)
    have all (z:ℕ) (lo:3≤z) (hi:z≤5) := bounded 3 z lo hi lo cap3
    have bound := interior_area_lower (r:=r+a) (D:=5) pos ht (L.entries n) m (L.entries_positive n pn) pm (by decide)
    change rowEnergy (L.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
    have sumU : interiorArea (L.entries n) m (r+a) 5=U 2+U 3+U 4+U 5 := by simp [interiorArea,U,Finset.sum_range_succ]
    rw [sumU] at bound
    change NB+(U 2+U 3+U 4+U 5)≤_ at bound
    have slot := original_two_threshold_slot_guard G K n hn (by decide : 3≤5) cap
    change 5*ρ+rootShortfall G K.roots 5+5*A≤5*(μ+c) at slot
    have gain : C 3+V≤M+U 3 ∨ C 4+V≤M+U 4 ∨ C 5+V≤M+U 5 := by
      rcases (show j=3 ∨ j=4 ∨ j=5 by omega) with z|z|z <;> rw [z] at mix <;> omega
    exact quintic_quaternary_energy a μ _ NB _ _ _ h ρ _ _ V (C 2) (C 3) (C 4) (C 5) (U 2) (U 3) (U 4) (U 5)
      rk fee width root (by omega) orig (by omega) two (all 3 (by decide) (by decide)) (all 4 (by decide) (by decide))
      (all 5 (by decide) (by decide)) gain

#print axioms quintic_full_retained_paid
end JSP452Audit.StarHost