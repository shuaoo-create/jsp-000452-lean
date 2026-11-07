import OriginalRegionEdgeAccount
namespace JSP452Audit.StarHost

/-- A capped shorter head and both whole-list mass bounds pay the original
row using the original edge count, including the root degree shortfall. -/
theorem two_embedded_ledger_bound (D E N e a μ k d ρ h t u v : ℕ)
    (six : 6≤D) (inside : t≤μ) (width : h≤ρ)
    (rank : N=a+μ+k+d) (massU : u+d≤a+μ+ρ) (massV : v+d≤a+μ+ρ)
    (profile : E≤N+(D-3)*t+u+v+h)
    (original : 2*D*(a+μ)+D*ρ+2*k≤2*e+D*a) : E≤e := by
  have scale := Nat.mul_le_mul_left (D-3) inside
  have roots := Nat.mul_le_mul_right a six
  have holes := Nat.mul_le_mul_right ρ six
  have dμ : D*μ=(D-3)*μ+3*μ := by
    calc
      D*μ=(D-3+3)*μ := by rw [show D-3+3=D by omega]
      _ = _ := Nat.add_mul _ _ _
  rw [Nat.mul_add,Nat.mul_assoc 2 D a,Nat.mul_assoc 2 D μ] at original
  omega

theorem double_embedded_profile_exclusion {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D)
    (lengths : s≤t) (before : r<s) (head : n ⟨0,hs⟩<D) (top : diagonal n m (r+2)=D+1)
    (six : 6≤D) (cap : ∀v,Nat.card (G.neighborSet v)≤D) (width : highestWidth n m r≤minimumExposure G D)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)) : rowEnergy n m r≤G.edgeSet.ncard := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let k := matchingEdges (G.induce K.rest)
  let ρ := minimumExposure G D
  have parts := region_rank_partition G K.barrier K.tight K.pieces
  change matchingEdges G=a+μ+k at parts
  have count : rowCount s t r=a+μ+k+d := by omega
  have q := nontrivial_core_count_le_region_pieces G D K
  change nontrivialCoreCount (G.induce K.core)≤a+ρ at q
  have rm : (∑i,n i)+d≤a+μ+ρ := by
    rcases red with small|⟨_,large,_⟩
    · change μ+d+1≤s at small;change t≤μ at embedded;omega
    · change (∑i,n i)+d≤μ+nontrivialCoreCount (G.induce K.core) at large;omega
  have bm : (∑j,m j)+d≤a+μ+ρ := by
    rcases blue with small|⟨_,large,_⟩
    · change μ+d+1≤t at small;change t≤μ at embedded;omega
    · change (∑j,m j)+d≤μ+nontrivialCoreCount (G.induce K.core) at large;omega
  exact two_embedded_ledger_bound D _ _ _ a μ k d ρ _ t _ _ six embedded width count rm bm
    (shorter_head_profile_bound hs ht n m hn hm pn pm lengths before (by omega) (by omega) top)
    (ordinary_region_edge_floor G D cap K)

#print axioms two_embedded_ledger_bound
#print axioms double_embedded_profile_exclusion
end JSP452Audit.StarHost
