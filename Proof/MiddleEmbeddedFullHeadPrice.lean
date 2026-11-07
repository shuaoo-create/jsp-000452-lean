import CoreRankRootCost
import MiddleDegreeDominatingAccount
import StrictActualRootBudget
import DoubleEmbeddedShortHeadExclusion
namespace JSP452Audit.StarHost
open SimpleGraph

/-- Both genuinely embedded lists, with the shorter head at full degree,
pay the original finite graph under the actual-weight selector budget. -/
theorem middle_embedded_full_head_paid {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (large : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (width : highestWidth n m r≤minimumExposure G D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (d : ℕ)
    (exposed : 1≤minimumExposure G D) (deficit : minimumExposure G D+1≤d)
    (budget : D*minimumExposure G D+rootShortfall G K.roots D+crossCount G K.roots K.rest+2≤2*highestWidth n m r+24)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)) : rowEnergy n m r≤G.edgeSet.ncard := by
  let μ := matchingEdges (G.induce K.core)
  let M := K.roots.ncard+μ
  let k := matchingEdges (G.induce K.rest)
  let B := (G.induce K.rest).edgeSet.ncard
  let z := B-k
  let ζ := rootShortfall G K.roots D
  let β := crossCount G K.roots K.rest
  let ρ := minimumExposure G D
  let h := highestWidth n m r
  let u := ∑i,n i
  let v := ∑j,m j
  let E := rowEnergy n m r
  let e := G.edgeSet.ncard
  have q := nontrivial_core_count_le_region_pieces G D K
  change nontrivialCoreCount (G.induce K.core)≤K.roots.ncard+ρ at q
  change t≤μ at embedded
  have rm : u+d≤M+ρ := by
    rcases red with small|⟨_,mass,_⟩
    · change μ+d+1≤s at small;omega
    · change u+d≤μ+nontrivialCoreCount (G.induce K.core) at mass;dsimp [M];omega
  have bm : v+d≤M+ρ := by
    rcases blue with small|⟨_,mass,_⟩
    · change μ+d+1≤t at small;omega
    · change v+d≤μ+nontrivialCoreCount (G.induce K.core) at mass;dsimp [M];omega
  have en := original_full_head_profile hs ht n m hn hm pn pm order before (by omega) head.le top
  change E+t≤(t-1-r)*D+u+v+h at en
  have enQ : (E:ℚ)+t≤((t-1-r:ℕ):ℚ)*D+u+v+h := by exact_mod_cast en
  rw [Nat.cast_sub (by omega : r≤t-1),Nat.cast_sub (by omega : 1≤t),Nat.cast_one] at enQ
  have eq := ordinary_region_original_edge_account G D cap K
  change 2*e+ζ=2*D*M+D*ρ+β+2*B at eq
  have kB : k≤B := matchingEdges_le_edgeCount _
  have fixB : B=k+z := by dsimp [z];omega
  rw [fixB] at eq
  have cost := ordinary_core_rank_caps_root_cost G D K cap
  change D*ρ+ζ+β≤2*μ at cost
  have frac := original_head_dominating_price G D (by omega) K hs n m pm cap head (by omega) row
  change ((D:ℚ)-1)*((t-r:ℕ):ℚ) ≤ ((D:ℚ)-1)*(1/4+(3/4:ℚ)^(D+1))*((2*M+ρ:ℕ):ℚ)+(z:ℚ)+β at frac
  rw [Nat.cast_sub (by omega : r≤t),Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at frac
  have Dq : (6:ℚ)≤D := by exact_mod_cast large
  have cheaper := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (quarter_bound_at_six D large) (by linarith : 0≤(D:ℚ)-1))
    (by positivity : (0:ℚ)≤2*(M:ℚ)+ρ)
  have dom : ((D:ℚ)-1)*(t-r)≤((D:ℚ)-1)*(7/18)*(2*M+ρ)+z+β := by linarith
  have small : μ≤M := by dsimp [M];omega
  have total : D*ρ+ζ+β≤2*M := by omega
  change D*ρ+ζ+β+2≤2*h+24 at budget
  have bound := middle_degree_dominating_account (D:ℚ) E e M k z ζ β ρ h t r d u v Dq
    (by positivity) (by positivity) (by positivity) (by exact_mod_cast exposed)
    (by exact_mod_cast deficit) (by exact_mod_cast width) (by exact_mod_cast rm) (by exact_mod_cast bm)
    enQ (by exact_mod_cast eq) (by exact_mod_cast total) (by exact_mod_cast budget) dom
  change E≤e
  have one : (1:ℚ)≤ρ := by exact_mod_cast exposed
  have paid : (E:ℚ)≤e := by linarith only [bound,one]
  exact_mod_cast paid

#print axioms middle_embedded_full_head_paid
end JSP452Audit.StarHost
