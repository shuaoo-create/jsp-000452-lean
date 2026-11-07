import CubicBinaryPeak
namespace JSP452Audit.StarHost
open SimpleGraph

/-- In the actual shorter-side cubic orientation the opposite original head
has exactly two leaves. Both counts in the peak now give an exact width. -/
theorem cubic_ordered_opposite_binary {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D) (three : D=3)
    (order : s≤t) (before : r<s) (nHead : n ⟨0,hs⟩=D) (mHead : m ⟨0,ht⟩≤D)
    (top : diagonal n m (r+2)=D+1) (live : 0<rowCount s t r) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (width : highestWidth n m r≤minimumExposure G D) (d : ℕ) (balance : matchingEdges G+d=rowCount s t r)
    (deficit : minimumExposure G D+1≤d) (budget : 3*minimumExposure G D+rootShortfall G K.roots D≤
      2*highestWidth n m r+2) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) (far : s+r+highestWidth n m r≤t)
    (strict : G.edgeSet.ncard<rowEnergy n m r) :
    m ⟨0,ht⟩=2 ∧ originalThresholdCount n 3+originalThresholdCount m 2=highestWidth n m r+r+1 := by
  subst D
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let M := a+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let ζ := rootShortfall G K.roots 3
  let β := crossCount G K.roots K.rest
  let ρ := minimumExposure G 3
  let h := highestWidth n m r
  let A := originalThresholdCount n 2
  let P := originalThresholdCount n 3
  let b := originalThresholdCount m 2
  let q := originalThresholdCount m 3
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  have ncap (i:Fin s) : n i≤3 := (hn (show (⟨0,hs⟩:Fin s)≤ i from Nat.zero_le _)).trans_eq nHead
  obtain ⟨i,j,_,atTop⟩ := diagonal_attained n m hs ht r (by dsimp [rowCount] at live;omega)
  have nle := ncap i
  have redLeaf := cubic_original_leaf_sum n pn ncap
  have high : 2≤m ⟨0,ht⟩ := by
    have mj := hm (show (⟨0,ht⟩:Fin t)≤ j from Nat.zero_le _);omega
  have peak := width_at_actual_top (r:=r) hs ht n m hn hm
  rw [top] at peak
  have n2 : 0<A := (original_threshold_prefix n hn 2 ⟨0,hs⟩).1 (by omega)
  have n3 : 0<P := (original_threshold_prefix n hn 3 ⟨0,hs⟩).1 nHead.ge
  have m2 : 0<b := (original_threshold_prefix m hm 2 ⟨0,ht⟩).1 high
  have first := actual_rectangle_le_column (r:=r) n m hn hm (by decide : 3+2-1=4) n3 m2
  rw [peak] at first;change P+b-1-r≤h at first
  have two : m ⟨0,ht⟩=2 := by
    by_contra no
    have mh : 3≤m ⟨0,ht⟩ := by omega
    have m3 : 0<q := (original_threshold_prefix m hm 3 ⟨0,ht⟩).1 mh
    have second := actual_rectangle_le_column (r:=r) n m hn hm (by decide : 2+3-1=4) n2 m3
    rw [peak] at second;change A+q-1-r≤h at second
    have part := region_rank_partition G K.barrier K.tight K.pieces
    change matchingEdges G=M+k at part
    have rank : M+k+d+r+1=s+t := by dsimp [rowCount] at balance live;omega
    obtain ⟨half,_,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤t);change t≤μ+d at embedded;omega)
    change t+d+2*(∑j,(m j-1)/2)≤μ+1 at half
    have guard : k+a+2*d+r≤s := by dsimp [M] at rank;omega
    have edge := ordinary_region_original_edge_account G 3 cap K
    change 2*e+ζ=6*M+3*ρ+β+2*B at edge
    have axis := embedded_head_axis_upper hs ht n m hn hm pm nHead top far
    change E≤(t-1-r)*3+(∑i,n i)+h at axis
    change (∑i,n i)=s+A+P at redLeaf
    have upper : E≤s+A+P+3*(t-1-r)+h := by omega
    have yes := two_cubic_heads_pay_axis s t r E e M a k B ζ β ρ h d A P b q (before.trans_le order)
      rank guard width deficit first second m2 m3 upper edge (matchingEdges_le_edgeCount _) budget
    change e<E at strict;omega
  exact ⟨two,(cubic_binary_peak_width hs ht n m hn hm pn pm nHead.le two.le live top).2.2⟩

#print axioms cubic_ordered_opposite_binary
end JSP452Audit.StarHost
