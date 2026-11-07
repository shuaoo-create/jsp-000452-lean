import ActualJointBlueAxis
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem all_full_unit_exteriors_impossible {s t r D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) (degree:6≤D) (cap:∀v,Nat.card (G.neighborSet v)≤D)
    (live : 0<rowCount s t r) (head : n ⟨0,hs⟩=D) (large : 3≤m ⟨0,ht⟩) (sub : m ⟨0,ht⟩<D)
    (top : diagonal n m (r+2)=D+1)
    (d : ℕ)
    (data : BothActualSuccessors G K n m r (rowCount s t r) d (rowEnergy n m r))
    (esc : matchingEdges (G.induce K.core)<s) (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (outer : K.roots.ncard+r+2*d≤s-matchingEdges (G.induce K.core))
    (width : 1≤highestWidth n m r ∧ highestWidth n m r≤minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (trigger : FullMixedBoundary n m ht r D (matchingEdges (G.induce K.core)))
    (unit : originalThresholdCount ((componentBudget (G.induce K.core) n).entries n) 2=0) : False := by
  let a := K.roots.ncard
  let H := G.induce K.core
  let μ := matchingEdges H
  let W := componentBudget H n
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let B := originalThresholdCount m 2
  let b := m ⟨0,ht⟩
  let g := originalThresholdCount m
  let C := widthAt n m r
  let Q := basicCapacity G K n m r
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
  let V := μ-A
  let S := s-μ
  let δ := μ-W.loss
  let J := commonErasedDemand n W a μ
  have eqVA : μ=V+A := by dsimp [V];omega
  have sl : s=μ+S := by dsimp [S];omega
  have basic (v:ℕ) : a+2*μ≤Q v := by
    change a+2*μ≤a+2*μ+widthAt (W.entries n) m (r+a) v+widthAt J m r v
    omega
  have above (v:ℕ) (lo:3≤v) (hi:v≤D) (big:b<v) : C v≤A-1 := by
    have bound := (rows v lo hi).2 big
    change C v≤A+g b-1-r at bound
    change g b≤r at gb
    omega
  have mid (v:ℕ) (lo:3≤v) (hi:v<D) : 2*C v≤Q v := by
    by_cases low : v≤b
    · have bound := (rows v lo hi.le).1 low
      change C v≤s+g v-1-r at bound
      have pos := (original_threshold_prefix m hm v ⟨0,ht⟩).1 low
      have blue := (joint_common_blue_axis G K n m hn hm pn esc r v pos).1
      change 2*(s+g v-1-r)≤Q v at blue;omega
    · have bound := above v lo hi.le (by omega)
      have base := basic v;omega
  have upper : 2*C D+(a+2*V+2)≤Q D := by
    have bound := above D (by omega) le_rfl bd
    have base := basic D;omega
  have low := joint_common_blue_axis G K n m hn hm pn esc r 2 bpos
  change 2*(s+B-1-r)≤Q 2 ∧ 2*s+2*B≤Q 2+2+2*r at low
  have winner := full_head_two_layer_options hs ht n m hn hm pn pm (actual_height_positive n m live top 2 (by omega))
  have volume := unit_residual_nonunit_volume G K n hn esc unit
  change μ≤3*V+a+ρ at volume
  have order := threshold_anti_height m (by omega : 2≤b)
  change g b≤B at order
  change originalThresholdCount n (b+1)+t<A+g b at over
  have charge := joint_unit_endpoint_balance D s t r μ a S V A B h ρ (C 2) (Q 2) (a+2*V+2) δ (by omega) wh sl
    (by dsimp [S];omega) eqVA volume (by omega) (by omega) winner low le_rfl
  have strict := raw_strict_joint_total G K n m r _ d hs ht hn hm pn pm (by omega) top rfl esc cap data
  change (∑z∈Finset.range (D-1),Q (z+2))+D*ρ+2*δ<2*(∑z∈Finset.range (D-1),C (z+2))+2*h at strict
  exact joint_unit_top_contradiction D h ρ δ (a+2*V+2) C Q (by omega) strict mid upper charge

#print axioms all_full_unit_exteriors_impossible
end JSP452Audit.StarHost