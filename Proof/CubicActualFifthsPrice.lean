import CubicFifthsAxisPayment
namespace JSP452Audit.StarHost
open SimpleGraph

/-- The actual cubic 3/2 axis is paid by a full-degree dominating set
satisfying the displayed two-fifths transfer price. -/
theorem cubic_full_axis_price_from_set {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G 3)
    (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩=3) (opposite : m ⟨0,ht⟩=2)
    (top : diagonal n m (r+2)=4) (cap : ∀v,Nat.card (G.neighborSet v)≤3)
    (width : highestWidth n m r≤minimumExposure G 3)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r) (short : d<s)
    (exposed : 1≤minimumExposure G 3) (small : minimumExposure G 3≤2) (deficit : minimumExposure G 3+1≤d)
    (budget : 3*minimumExposure G 3+(rootShortfall G K.roots 3+2*(G.induce K.roots).edgeSet.ncard+
      crossCount G K.roots K.rest)≤2*highestWidth n m r+2)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) (far : s+r+highestWidth n m r≤t)
    (S:Set X) (dom : ∀v,Nat.card (G.neighborSet v)=3 → v∈S ∨ ∃w∈S,G.Adj v w)
    (price : 10*S.ncard≤8*(K.roots.ncard+matchingEdges (G.induce K.core))+4*minimumExposure G 3+
      5*((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest))+5*crossCount G K.roots K.rest) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let M := a+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let z := B-k
  let ζ := rootShortfall G K.roots 3
  let β := crossCount G K.roots K.rest
  let L := ζ+2*(G.induce K.roots).edgeSet.ncard+β
  let ρ := minimumExposure G 3
  let h := highestWidth n m r
  let u := ∑j,n j
  let V := u-s
  let f := originalThresholdCount n 3
  let i := min r (f-1)
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  have need := full_prefix_dominating_price G hs n m hn pm (before.trans_le order) cap (by decide) head row S dom
  change t-r+i≤S.ncard at need
  change 10*S.ncard≤8*M+4*ρ+5*z+5*β at price
  have cut : 10*(t-r+i)≤8*M+4*ρ+5*z+5*β := by omega
  have cq : 10*(((t-r:ℕ):ℚ)+i)≤8*(M:ℚ)+4*ρ+5*z+5*β := by exact_mod_cast cut
  rw [Nat.cast_sub (by omega : r≤t)] at cq
  have part := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=M+k at part
  have rank : M+k+d+r+1=s+t := by dsimp [rowCount] at balance live;omega
  have qRank : (M:ℚ)+k+d=(s:ℚ)+t-r-1 := by
    have q : (M:ℚ)+k+d+r+1=(s:ℚ)+t := by exact_mod_cast rank
    linarith
  have edge := ordinary_region_original_edge_account G 3 cap K
  change 2*e+ζ=6*M+3*ρ+β+2*B at edge
  have kB : k≤B := matchingEdges_le_edgeCount _
  have split : B=k+z := by dsimp [z];omega
  have edgeL : 6*M+3*ρ+2*k+2*z+2*β≤2*e+L := by dsimp [L];omega
  have halfMass := cubic_embedded_half_mass G K n pn d short cap (order.trans embedded) red
  change u+d+(μ+d-s)/2≤M+ρ at halfMass
  have ncap (j:Fin s) : n j≤3 := (hn (show (⟨0,hs⟩:Fin s)≤ j from Nat.zero_le _)).trans_eq head
  have entries := cubic_original_leaf_sum n pn ncap
  let A := originalThresholdCount n 2
  change u=s+A+f at entries
  have aSize : A≤s := original_threshold_le_length _ _
  have leaf : V≤s+f := by dsimp [V];omega
  change t≤μ+d at embedded
  have weighted : 2*V+s+3*d≤M+a+2*ρ+1 := by dsimp [M] at halfMass ⊢;dsimp [V];omega
  have qWeighted : 2*(V:ℚ)≤M+a-s+2*ρ-3*d+1 := by
    have q : 2*(V:ℚ)+s+3*d≤M+a+2*ρ+1 := by exact_mod_cast weighted
    linarith
  obtain ⟨half,_,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤t);omega)
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at half
  have tail : t+d≤μ+1 := by omega
  obtain ⟨fpos,bpos,peak⟩ := cubic_binary_peak_width hs ht n m hn hm pn pm head.le opposite.le live top
  change 0<f at fpos
  change f+originalThresholdCount m 2=h+r+1 at peak
  have fcap : f≤r+h := by omega
  have corner : (i:ℚ)=r ∨ (i:ℚ)=(f:ℚ)-1 := by
    by_cases le:r≤f-1
    · left;exact_mod_cast (Nat.min_eq_left le)
    · right
      have eq : i+1=f := by dsimp [i];omega
      have q : (i:ℚ)+1=f := by exact_mod_cast eq
      linarith
  have axis := embedded_head_axis_upper hs ht n m hn hm pm head top far
  change E≤(t-1-r)*3+u+h at axis
  have fee : E+3*r+3≤3*t+s+V+h := by dsimp [V];omega
  have qAxis : (E:ℚ)≤3*(t-r-1)+s+V+h := by
    have q : (E:ℚ)+3*r+3≤3*t+s+V+h := by exact_mod_cast fee
    linarith
  have pay := cubic_fifths_axis_payment (s:ℚ) t r a μ M k z β L ρ h d V f i E e
    (by exact_mod_cast (rfl : M=a+μ)) qRank (by exact_mod_cast exposed) (by exact_mod_cast small)
    (by exact_mod_cast width) (by exact_mod_cast deficit) (by exact_mod_cast budget)
    (by exact_mod_cast leaf) qWeighted (by exact_mod_cast tail) (by exact_mod_cast fpos)
    (by exact_mod_cast fcap) corner cq qAxis (by exact_mod_cast edgeL)
    (by positivity) (by positivity) (by positivity) (by positivity) (by positivity)
  change E≤e
  exact_mod_cast pay

#print axioms cubic_full_axis_price_from_set
end JSP452Audit.StarHost
