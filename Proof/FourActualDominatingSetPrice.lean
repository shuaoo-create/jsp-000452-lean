import FourFullHeadLeafTerms
namespace JSP452Audit.StarHost
open SimpleGraph

/-- A specific finite dominating set with this size pays the actual
four-degree row. Its existence still has to be constructed separately. -/
theorem four_full_head_price_from_set {s t r : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G 4)
    (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩=4) (top : diagonal n m (r+2)=5)
    (cap : ∀v,Nat.card (G.neighborSet v)≤4) (width : highestWidth n m r≤minimumExposure G 4)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r) (short : d<s)
    (exposed : 1≤minimumExposure G 4) (deficit : minimumExposure G 4+1≤d)
    (budget : 4*minimumExposure G 4+(rootShortfall G K.roots 4+2*(G.induce K.roots).edgeSet.ncard+
      crossCount G K.roots K.rest)≤2*highestWidth n m r+10)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) (far : s+r+highestWidth n m r≤t)
    (S:Set X) (dom : ∀v,Nat.card (G.neighborSet v)=4 → v∈S ∨ ∃w∈S,G.Adj v w)
    (price : 87*S.ncard≤66*(K.roots.ncard+matchingEdges (G.induce K.core))+33*minimumExposure G 4+
      29*((G.induce K.rest).edgeSet.ncard-matchingEdges (G.induce K.rest))+33*crossCount G K.roots K.rest) :
    rowEnergy n m r≤G.edgeSet.ncard := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let M := a+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let z := B-k
  let ζ := rootShortfall G K.roots 4
  let β := crossCount G K.roots K.rest
  let L := ζ+2*(G.induce K.roots).edgeSet.ncard+β
  let ρ := minimumExposure G 4
  let h := highestWidth n m r
  let u := ∑i,n i
  let V := u-s
  let f := originalThresholdCount n 4
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  have need := dominating_set_pays_blue_suffix G 4 (by decide) hs n m pm cap head (by omega) row S dom
  change 87*S.ncard≤66*M+33*ρ+29*z+33*β at price
  have cut : 87*(t-r)≤66*M+33*ρ+29*z+33*β := by omega
  have tau : t-r+r=t := by omega
  have cq : 87*((t-r:ℕ):ℚ)≤66*(M:ℚ)+33*ρ+29*z+33*β := by exact_mod_cast cut
  rw [Nat.cast_sub (by omega : r≤t)] at cq
  have part := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=M+k at part
  have rank : M+k+d+r+1=s+t := by dsimp [rowCount] at balance live;omega
  have qRank : (M:ℚ)+k+d=(s:ℚ)+t-r-1 := by
    have q : (M:ℚ)+k+d+r+1=(s:ℚ)+t := by exact_mod_cast rank
    linarith
  have edge := ordinary_region_original_edge_account G 4 cap K
  change 2*e+ζ=8*M+4*ρ+β+2*B at edge
  have kB : k≤B := matchingEdges_le_edgeCount _
  have split : B=k+z := by dsimp [z];omega
  have edgeL : 8*M+4*ρ+2*k+2*z+2*β≤2*e+L := by dsimp [L];omega
  have root := root_cost_complement G 4 K cap
  change L+crossCount G K.roots K.core=4*a at root
  have roots : L≤4*a := by omega
  have finer := embedded_robust_mass_weighted G K n pn d short (by decide) cap (order.trans embedded) red
  change 4*u+5*d+1≤3*μ+s+4*(a+ρ)+4 at finer
  have small (i:Fin s) : n i≤4 := (hn (show (⟨0,hs⟩:Fin s)≤ i from Nat.zero_le _)).trans_eq head
  obtain ⟨base,entryCap,hc⟩ := four_full_head_leaf_terms hs ht n m hn hm pn small head live top
  change s≤u at base
  have splitU : u=s+V := by dsimp [V];omega
  change u≤3*s+f at entryCap
  have together : V≤2*s+f := by omega
  have weighted : 4*V+3*s+5*d≤3*M+a+4*ρ+3 := by dsimp [M];omega
  have qWeighted : 4*(V:ℚ)≤3*M+a-3*s+4*ρ-5*d+3 := by
    have q : 4*(V:ℚ)+3*s+5*d≤3*M+a+4*ρ+3 := by exact_mod_cast weighted
    linarith
  obtain ⟨half,_,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤t);change t≤μ+d at embedded;omega)
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at half
  have tail : t+d≤μ+1 := by omega
  have axis := embedded_head_axis_upper hs ht n m hn hm pm head top far
  change E≤(t-1-r)*4+u+h at axis
  have fee : E+4*r+4≤4*t+s+V+h := by omega
  have qAxis : (E:ℚ)≤4*t-4*r+s+V+h-4 := by
    have q : (E:ℚ)+4*r+4≤4*t+s+V+h := by exact_mod_cast fee
    linarith
  have paid := four_axis_domination_payment (s:ℚ) t r M a μ k z e E ρ h d L β V f
    (by exact_mod_cast (rfl : M=a+μ)) qRank (by exact_mod_cast deficit) (by exact_mod_cast exposed)
    (by exact_mod_cast width) (by exact_mod_cast budget) (by exact_mod_cast roots)
    (by exact_mod_cast together) (by exact_mod_cast tail) qWeighted (by exact_mod_cast hc) cq qAxis
    (by positivity) (by positivity) (by positivity) (by exact_mod_cast edgeL)
  have final : (E:ℚ)≤e := by linarith only [paid]
  change E≤e
  exact_mod_cast final

#print axioms four_full_head_price_from_set
end JSP452Audit.StarHost
