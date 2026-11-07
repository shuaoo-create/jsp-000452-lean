import QuinticUnitLargeArithmetic
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem quintic_full_unit_large_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (five:D=5) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (heads : m ⟨0,ht⟩=3 ∨ m ⟨0,ht⟩=4) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d) (root : 3*minimumExposure G D+rootShortfall G K.roots D≤10)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) : rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let Z := G.induce K.rest
  let ρ := minimumExposure G 5
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let b := m ⟨0,ht⟩
  let g := originalThresholdCount m
  let C := widthAt n m r
  let U := widthAt (W.entries n) m (r+a)
  let NB := rowCount W.len t (r+a)
  have bh : b=3 ∨ b=4 := heads
  have full := (original_threshold_prefix n hn 5 ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by change 2≤b;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=5) (b:=2) (h:=6) (by decide) full bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change originalThresholdCount n 5+B-1-r≤h at rect
  have wh : h≤ρ := width.2
  have limit : B≤r+ρ := by omega
  change μ<s at esc
  change a+r+2*d≤s-μ at outer
  change ρ+1≤d at reserve
  change a+r+2*(d+∑i,(n i-1)/2)≤t at endpoint
  have space : μ+B≤s := by omega
  have redcap : (∑i,(n i-1)/2)+B≤t := by omega
  have half := unit_residual_full_half_budget G K n hn esc unit
  change A+(∑i,(n i-1)/2)≤μ at half
  have fitA : A≤μ := by omega
  obtain ⟨j,y,_,_,_,_,over,_,last⟩ := trigger
  obtain ⟨yb,jb⟩ := last fitA
  change y=b at yb;change j=b+1 at jb
  rw [yb,jb] at over
  have gb := large_opposite_prefix_before_offset hs n m hm head top (show 3≤b by omega)
  have rows (v:ℕ) (lo:3≤v) (hi:v≤5) := full_unit_large_layer hs ht n m hn hm pn pm (b:=b) rfl lo
    (actual_height_positive n m live top v (by omega)) half space redcap over
  have pA : 0<A := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by omega)
  obtain ⟨_,fit,_,bsize,_,_,_,cheap⟩ := data
  change W.loss≤μ at fit
  have pos : 0<W.len := by dsimp only [RemovalBudget.len];omega
  have len : s≤W.len+μ := by dsimp only [RemovalBudget.len];omega
  have size : s-μ≤W.len := by omega
  let k := matchingEdges Z
  change NB=k+d+(μ-W.loss) at bsize
  have split := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at split
  have rn : rowCount s t r≤NB+a+μ := by omega
  have uni := original_threshold_one (W.entries n) (W.entries_positive n pn)
  have ext (v:ℕ) (posV:v≤b) : W.len+g v-1-(r+a)≤U v := by
    have gp := (original_threshold_prefix m hm v ⟨0,ht⟩).1 posV
    have e := actual_rectangle_le_column (r:=r+a) (W.entries n) m (W.entries_antitone n hn) hm
      (a:=1) (b:=v) (h:=v) (by omega) (uni.symm ▸ pos) gp
    rwa [uni] at e
  have low (v:ℕ) (lo:3≤v) (hi:v≤5) (vb:v≤b) : C v≤a+μ+U v := by
    have l := (rows v lo hi).1 vb
    change C v≤s+g v-1-r at l
    have e := ext v vb
    omega
  have high (v:ℕ) (lo:3≤v) (hi:v≤5) (vb:b<v) : C v≤A-1 := by
    have l := (rows v lo hi).2 vb
    change C v≤A+g b-1-r at l
    change g b≤r at gb
    omega
  have mid := quintic_unit_middle_total a μ A b (C 3) (C 4) (C 5) (U 3) (U 4) (U 5) bh fitA pA
    (low 3 (by decide) (by decide) (by omega)) (low 4 (by decide) (by decide)) (high 4 (by decide) (by decide))
    (high 5 (by decide) (by decide) (by omega))
  have orig := original_area_by_height hs ht n m hn hm pn pm top (by decide)
  have rowsum : interiorArea n m r 5=C 2+C 3+C 4+C 5 := by simp [interiorArea,C,Finset.sum_range_succ]
  rw [rowsum] at orig
  have area : rowEnergy n m r≤rowCount s t r+C 2+(C 3+C 4+C 5)+h := by change _=_+_+h at orig;omega
  have layer := interior_area_lower (r:=r+a) (D:=5) pos ht (W.entries n) m (W.entries_positive n pn) pm (by decide)
  change rowEnergy (W.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
  have sumU : interiorArea (W.entries n) m (r+a) 5=U 2+U 3+U 4+U 5 := by simp [interiorArea,U,Finset.sum_range_succ]
  rw [sumU] at layer
  change NB+(U 2+U 3+U 4+U 5)≤_ at layer
  have edges : NB+U 2+(U 3+U 4+U 5)≤Z.edgeSet.ncard := by omega
  have winner := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by decide))
  have two := ext 2 (by omega)
  change W.len+B-1-(r+a)≤U 2 at two
  have volume := unit_residual_nonunit_volume G K n hn esc unit
  change μ≤3*(μ-A)+a+ρ at volume
  have order := threshold_anti_height m (by omega : 2≤b)
  change originalThresholdCount n (b+1)+t<A+g b at over
  exact quintic_unit_large_price s t r a μ _ NB _ _ _ h ρ _ _ d A B (g b) (C 2) (U 2) _ _ rn
    (ordinary_region_original_edge_account G 5 cap K) width reserve outer (by omega) root (Nat.sub_le _ _)
    fitA (by omega) (by omega) order area (by simpa only [Nat.add_assoc] using mid) winner (by omega) edges

#print axioms quintic_full_unit_large_paid
end JSP452Audit.StarHost