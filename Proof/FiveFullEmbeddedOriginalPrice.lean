import FiveMatchedAxisIntegerPrice
import LargeEmbeddedFullHeadPrice
namespace JSP452Audit.StarHost
open SimpleGraph

/-- At degree five a full shorter head on the original strict graph is
paid, with a separate genuine original-row estimate for each length range. -/
theorem five_matched_full_head_paid {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D) (five : D=5)
    (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (width : highestWidth n m r≤minimumExposure G D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r) (short : d<s)
    (exposed : 1≤minimumExposure G D) (deficit : minimumExposure G D+1≤d)
    (budget : 3*minimumExposure G D+rootShortfall G K.roots D+crossCount G K.roots K.rest≤10)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) : rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let M := a+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let z := B-k
  let ζ := rootShortfall G K.roots 5
  let β := crossCount G K.roots K.rest
  let ρ := minimumExposure G 5
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
  have q := nontrivial_core_count_le_region_pieces G 5 K
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
  have edges := ordinary_region_original_edge_account G 5 cap K
  change 2*e+ζ=10*M+5*ρ+β+2*B at edges
  have kB : k≤B := matchingEdges_le_edgeCount _
  have fixB : B=k+z := by dsimp [z];omega
  rw [fixB] at edges
  have guardR : k+a+2*d+r≤s := by dsimp [M] at rank;omega
  have guards : k+2*a+3*d+r≤M+1 := by dsimp [M] at rank ⊢;omega
  have stronger := embedded_robust_mass_weighted G K n pn d short (by decide) cap inner red
  change 5*u+6*d+1≤4*μ+s+5*(a+ρ)+5 at stronger
  have ncap (i:Fin s) : n i≤5 := (hn (show (⟨0,hs⟩:Fin s)≤ i from Nat.zero_le _)).trans_eq head
  have entry := five_original_red_mass_upper hs ht n m hn hm ncap head live top
  have general := original_full_head_profile hs ht n m hn hm pn pm order before (by decide : 3≤5) head.le top
  have long (room : s+r+h≤t) := embedded_head_axis_upper hs ht n m hn hm pm head top room
  have matched := five_original_matched_blue_price G K hs n m pm cap head (by omega) row
  change 4*((t-r:ℕ):ℚ)+(8/50:ℚ)*μ≤4*(21/50:ℚ)*((2*M+ρ:ℕ):ℚ)+(z:ℚ)+β at matched
  rw [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at matched
  have scaled : 200*((t-r:ℕ):ℚ)+8*μ≤84*(2*(M:ℚ)+ρ)+50*z+50*β := by linarith only [matched]
  have pricing : 200*(t-r)+8*μ≤84*(2*M+ρ)+50*z+50*β := by exact_mod_cast scaled
  change 1≤ρ at exposed
  change ρ+1≤d at deficit
  exact five_matched_axis_integer_price s t r N E e M a μ k z ζ β ρ h d u v before order rfl
    rank count exposed deficit width redM blueM edges budget guardR guards (by omega) general long stronger entry pricing

#print axioms five_matched_full_head_paid
end JSP452Audit.StarHost
