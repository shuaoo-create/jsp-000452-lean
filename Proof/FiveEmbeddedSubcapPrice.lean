import LowDegreeRegionGuards
import DoubleEmbeddedEdgePrice
namespace JSP452Audit.StarHost
open SimpleGraph

/-- In degree five the original root cost, together with the extra length
in the deficit, suffices even if the other original head reaches five. -/
theorem five_shorter_subcap_paid {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j) {X : Type*} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (five : D=5) (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩<D)
    (top : diagonal n m (r+2)=D+1) (cap : ∀v,Nat.card (G.neighborSet v)≤D)
    (width : highestWidth n m r≤minimumExposure G D) (exposed : 1≤minimumExposure G D)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r) (deficit : minimumExposure G D+1≤d)
    (short : t≤matchingEdges (G.induce K.core)+d)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (slack : 3*minimumExposure G D+rootShortfall G K.roots D≤10) : rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let k := matchingEdges (G.induce K.rest)
  let ρ := minimumExposure G 5
  let ζ := rootShortfall G K.roots 5
  let u := ∑i,n i
  let v := ∑j,m j
  let h := highestWidth n m r
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  change t≤μ+d at short
  obtain ⟨_,massR,_⟩ := red.resolve_left (by change ¬(μ+d+1≤s);omega)
  obtain ⟨half,massB,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤t);omega)
  change t+d+2*(∑i,(m i-1)/2)≤μ+1 at half
  change u+d≤μ+nontrivialCoreCount (G.induce K.core) at massR
  change v+d≤μ+nontrivialCoreCount (G.induce K.core) at massB
  have q := nontrivial_core_count_le_region_pieces G 5 K
  change nontrivialCoreCount (G.induce K.core)≤a+ρ at q
  have part := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at part
  have priced := shorter_head_profile_bound hs ht n m hn hm pn pm order before (by decide : 3≤5) (by omega) top
  change E≤rowCount s t r+2*t+u+v+h at priced
  have edge := ordinary_region_original_edge_account G 5 cap K
  change 2*e+ζ=10*(a+μ)+5*ρ+crossCount G K.roots K.rest+2*(G.induce K.rest).edgeSet.ncard at edge
  have ext : k≤(G.induce K.rest).edgeSet.ncard := matchingEdges_le_edgeCount _
  change 3*ρ+ζ≤10 at slack
  change h≤ρ at width
  change ρ+1≤d at deficit
  change 1≤ρ at exposed
  change E≤e
  omega

#print axioms five_shorter_subcap_paid
end JSP452Audit.StarHost
