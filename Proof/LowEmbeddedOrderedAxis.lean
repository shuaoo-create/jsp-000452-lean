import LowShorterAxisIntegerFrontier
namespace JSP452Audit.StarHost
open SimpleGraph

/-- In an original strict low-degree row with both lists embedded, the
shorter head reaches the cap and the opposite list extends past its width. -/
theorem low_embedded_ordered_axis {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (low : D=3 ∨ D=4) (order : s≤t) (before : r<s) (headCap : n ⟨0,hs⟩≤D)
    (top : diagonal n m (r+2)=D+1) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (width : highestWidth n m r≤minimumExposure G D) (d : ℕ) (balance : matchingEdges G+d=rowCount s t r)
    (exposed : 1≤minimumExposure G D) (deficit : minimumExposure G D+1≤d)
    (root3 : D=3 → minimumExposure G D≤2 ∧ 3*minimumExposure G D+rootShortfall G K.roots D≤2*highestWidth n m r+2)
    (root4 : D=4 → 4*minimumExposure G D+rootShortfall G K.roots D≤2*highestWidth n m r+10)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) (strict : G.edgeSet.ncard<rowEnergy n m r) :
    n ⟨0,hs⟩=D ∧ s+r+highestWidth n m r≤t ∧
      rowEnergy n m r≤(t-1-r)*D+(∑i,n i)+highestWidth n m r := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let M := a+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let ζ := rootShortfall G K.roots D
  let β := crossCount G K.roots K.rest
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let u := ∑i,n i
  let v := ∑j,m j
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  let N := rowCount s t r
  have count : N+r+1=s+t := by dsimp [N,rowCount];omega
  have part := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=M+k at part
  have rank : N=M+k+d := by change matchingEdges G+d=N at balance;omega
  have q := nontrivial_core_count_le_region_pieces G D K
  change nontrivialCoreCount (G.induce K.core)≤a+ρ at q
  change t≤μ+d at embedded
  have inner : s≤μ+d := order.trans embedded
  obtain ⟨halfR,rm,_⟩ := red.resolve_left (by change ¬(μ+d+1≤s);omega)
  obtain ⟨halfB,bm,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤t);omega)
  change s+d+2*(∑i,(n i-1)/2)≤μ+1 at halfR
  change t+d+2*(∑j,(m j-1)/2)≤μ+1 at halfB
  change u+d≤μ+nontrivialCoreCount (G.induce K.core) at rm
  change v+d≤μ+nontrivialCoreCount (G.induce K.core) at bm
  have redM : u+d≤M+ρ := by dsimp [M];omega
  have blueM : v+d≤M+ρ := by dsimp [M];omega
  have edges := ordinary_region_original_edge_account G D cap K
  change 2*e+ζ=2*D*M+D*ρ+β+2*B at edges
  have kB : k≤B := matchingEdges_le_edgeCount _
  have guards : k+2*a+3*d+r≤M+1 := by dsimp [M] at rank ⊢;omega
  have large : 3≤D := by omega
  have rootCap : ζ≤D*a := Nat.sub_le _ _
  have general := original_full_head_profile hs ht n m hn hm pn pm order before large headCap top
  have shortPrice (hc : n ⟨0,hs⟩<D) := shorter_head_profile_bound hs ht n m hn hm pn pm order before large
    (show n ⟨0,hs⟩≤D-1 by omega) top
  obtain ⟨head,far⟩ := low_shorter_axis_integer_frontier D (n ⟨0,hs⟩) s t r N E e a μ M k B ζ β ρ h d u v
    low headCap before order rfl rank count exposed width deficit (by omega) guards redM blueM kB edges rootCap
    root3 root4 shortPrice general strict
  exact ⟨head,far,embedded_head_axis_upper hs ht n m hn hm pm head top far⟩

#print axioms low_embedded_ordered_axis
end JSP452Audit.StarHost
