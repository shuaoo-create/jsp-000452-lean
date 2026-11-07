import NonunitJoinedResidualPays
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem twice_five_threshold_below_half {s : ℕ} (n : Fin s→ℕ) {x:ℕ} (high : 5≤x) :
    2*originalThresholdCount n x≤∑i,(n i-1)/2 := by
  have per (i:Fin s) : 2*(if x≤n i then 1 else 0)≤(n i-1)/2 := by split_ifs <;> omega
  have bound := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  rw [←Finset.mul_sum] at bound
  simpa [originalThresholdCount,Finset.sum_boole] using bound

/-- A top interior rectangle with both heads at least three, or one
with (D-1,2), pays all matching-axis losses and the source deficit. -/
theorem mixed_top_surplus {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d : ℕ)
    (pm : ∀j,1≤m j) (deg : 6≤D)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (space : t+d+2*(∑j,(m j-1)/2)≤matchingEdges (G.induce K.core)+1)
    (mass : (∑j,m j)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (winner : ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y) :
    2*widthAt n m r D+2*(∑i,(n i-1)/2)+2*d≤jointLayerCapacity G K D := by
  let a := K.roots.ncard
  let μ := matchingEdges (G.induce K.core)
  let ρ := minimumExposure G D
  let X₁ := ∑i,(n i-1)/2
  let Y := ∑j,(m j-1)/2
  obtain ⟨x,y,xhi,yhi,win⟩ := winner
  have wh := win.2.2.1
  have eq := win.2.2.2.2.2
  change a+r+2*(d+X₁)≤t at endpoint
  change t+d+2*Y≤μ+1 at space
  change (∑j,m j)+d≤μ+a+ρ at mass
  change ρ+1≤d at reserve
  have need : 2*widthAt n m r D+2*X₁+2*d≤a+2*μ := by
    by_cases low : y=2
    · subst y
      have heavy : 5≤x := by omega
      have cost := twice_five_threshold_below_half n heavy
      change 2*originalThresholdCount n x≤X₁ at cost
      have blue := units_and_twos_below_mass m pm
      omega
    · have ncost := half_extra_pays_large_threshold n xhi
      have mcost := half_extra_pays_large_threshold m (by omega : 3≤y)
      change originalThresholdCount n x≤X₁ at ncost
      change originalThresholdCount m y≤Y at mcost
      omega
  exact need.trans (by unfold jointLayerCapacity;omega)

theorem two_subcap_top_is_mixed {s t r D : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (live : 0<rowCount s t r) (top : diagonal n m (r+2)=D+1)
    (nc : n ⟨0,hs⟩<D) (mc : m ⟨0,ht⟩≤D-2) (deg : 6≤D) :
    ∃x y,3≤x ∧ 2≤y ∧ WinsHeight n m r D x y := by
  have present : 0<widthAt n m r D := by
    apply Finset.card_pos.mpr;exact ⟨0,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr live,by simp [top]⟩⟩
  obtain ⟨x,y,px,py,height,nx,my,eq⟩ := original_column_real_winner hs ht n m hn hm pn pm (by omega : 0<D) present
  have n0 := (original_threshold_prefix n hn x ⟨0,hs⟩).2 nx
  have m0 := (original_threshold_prefix m hm y ⟨0,ht⟩).2 my
  exact ⟨x,y,by omega,by omega,px,py,height,nx,my,eq⟩

#print axioms twice_five_threshold_below_half
#print axioms mixed_top_surplus
#print axioms two_subcap_top_is_mixed
end JSP452Audit.StarHost
