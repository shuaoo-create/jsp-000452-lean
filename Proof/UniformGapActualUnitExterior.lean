import FullUnitGapNaturalPrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem full_unit_uniform_gap_paid {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (degree:6≤D) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (large : 3≤m ⟨0,ht⟩) (sub : m ⟨0,ht⟩<D)
    (gap : D≤4*(D-m ⟨0,ht⟩-1)) (top : diagonal n m (r+2)=D+1)
    (d : ℕ) (rank : matchingEdges G+d=rowCount s t r)
    (data : CompleteExteriorData G K n m r (rowCount s t r) d)
    (esc : matchingEdges (G.induce K.core)<s) (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) : rowEnergy n m r≤G.edgeSet.ncard := by
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let Z := G.induce K.rest
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let b := m ⟨0,ht⟩
  let g := originalThresholdCount m
  let C := widthAt n m r
  let U := widthAt (W.entries n) m (r+a)
  let NB := rowCount W.len t (r+a)
  have bh : 3≤b := large
  have bd : b<D := sub
  have full := (original_threshold_prefix n hn D ⟨0,hs⟩).1 head.ge
  have bpos : 0<B := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 (by change 2≤b;omega)
  have rect := actual_rectangle_le_column (r:=r) n m hn hm (a:=D) (b:=2) (h:=D+1) (by omega) full bpos
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm;rw [top] at peak;rw [peak] at rect
  change originalThresholdCount n D+B-1-r≤h at rect
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
  have rows (v:ℕ) (lo:3≤v) (hi:v≤D) := full_unit_large_layer hs ht n m hn hm pn pm (b:=b) rfl lo
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
  have low (v:ℕ) (lo:3≤v) (hi:v≤D) (vb:v≤b) : C v≤a+μ+U v := by
    have l := (rows v lo hi).1 vb
    change C v≤s+g v-1-r at l
    have e := ext v vb
    omega
  have high (v:ℕ) (lo:3≤v) (hi:v≤D) (vb:b<v) : C v≤A-1 := by
    have l := (rows v lo hi).2 vb
    change C v≤A+g b-1-r at l
    change g b≤r at gb
    omega
  let V := μ-A
  let M := a+μ
  have eqVA : V+A=μ := by dsimp [V];omega
  have upper (v:ℕ) (vb:b<v) (hi:v≤D) : C v+(V+a+1)≤M+U v := by
    have priced := high v (by omega) hi vb
    dsimp [M];omega
  have middle := full_unit_middle_sum D b M V a C U bd.le bh (fun j jlo jb => low j jlo (by omega) jb) upper
  let SC := ∑z∈Finset.range (D-2),C (z+3)
  let SU := ∑z∈Finset.range (D-2),U (z+3)
  change SC+(D-b)*(V+a+1)≤(D-2)*M+SU at middle
  have orig := original_area_by_height hs ht n m hn hm pn pm top (by omega)
  rw [interior_peel_two n m r D (by omega)] at orig
  change rowEnergy n m r=rowCount s t r+(C 2+SC)+h at orig
  have area : rowEnergy n m r≤rowCount s t r+C 2+SC+h := by omega
  have layer := interior_area_lower (r:=r+a) (D:=D) pos ht (W.entries n) m (W.entries_positive n pn) pm (by omega)
  change rowEnergy (W.entries n) m (r+a)≤Z.edgeSet.ncard at cheap
  rw [interior_peel_two (W.entries n) m (r+a) D (by omega)] at layer
  change NB+(U 2+SU)≤_ at layer
  have edges : NB+U 2+SU≤Z.edgeSet.ncard := by omega
  have winner := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by omega))
  have two := ext 2 (by omega)
  change W.len+B-1-(r+a)≤U 2 at two
  have volume := unit_residual_nonunit_volume G K n hn esc unit
  change μ≤3*V+a+ρ at volume
  have order := threshold_anti_height m (by omega : 2≤b)
  change g b≤B at order
  change originalThresholdCount n (b+1)+t<A+g b at over
  have slot := original_two_threshold_slot_guard G K n hn (by omega) cap
  change D*ρ+rootShortfall G K.roots D+D*A≤D*(μ+originalThresholdCount (W.entries n) 2) at slot
  change originalThresholdCount (W.entries n) 2=0 at unit
  rw [unit,Nat.add_zero] at slot
  exact unit_gap_natural_payment s r D (D-b) a μ _ NB _ _ _ h ρ _ _ V A (s-μ) B t (C 2) (U 2) SC SU degree
    gap eqVA (by omega) slot (Nat.sub_le _ _) volume wh (by omega) (by omega) (by omega)
    (ordinary_region_original_edge_account G D cap K) rn area middle edges winner (by omega)

#print axioms full_unit_uniform_gap_paid
end JSP452Audit.StarHost