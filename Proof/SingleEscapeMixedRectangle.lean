import ActualOriginalAndExteriorEndpoints
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem threshold_anti_height {s : ℕ} (n : Fin s→ℕ) {x y : ℕ} (le:x≤y) :
    originalThresholdCount n y≤originalThresholdCount n x := by
  apply Finset.card_le_card
  exact fun i h => Finset.mem_filter.mpr ⟨Finset.mem_univ _,le.trans (Finset.mem_filter.mp h).2⟩

theorem half_extra_pays_large_threshold {s : ℕ} (n : Fin s→ℕ) {x : ℕ} (hi : 3≤x) :
    originalThresholdCount n x≤∑i,(n i-1)/2 := by
  have per (i:Fin s) : (if x≤n i then 1 else 0)≤(n i-1)/2 := by split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simpa [originalThresholdCount,Finset.sum_boole] using sum

theorem units_and_twos_below_mass {t : ℕ} (m : Fin t→ℕ) (pm : ∀j,1≤m j) :
    t+originalThresholdCount m 2≤∑j,m j := by
  have per (j:Fin t) : 1+(if 2≤m j then 1 else 0)≤m j := by have := pm j;split_ifs <;> omega
  have sum := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => per i)
  simpa [originalThresholdCount,Finset.sum_add_distrib,Finset.sum_boole] using sum

/-- A losing mixed rectangle needs strictly more escaping-side stars
than their half-order extra cost. Its red threshold is exactly two.
If its blue threshold is at least three, it must be the last blue level. -/
theorem single_escape_unpaid_rectangle {s t D : ℕ} {X : Type u} [Finite X] (G : SimpleGraph X)
    (K : DegreeRegion G D) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d j x y : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (endpoint : K.roots.ncard+r+2*(d+∑i,(n i-1)/2)≤t)
    (mass : (∑i,m i)+d≤matchingEdges (G.induce K.core)+K.roots.ncard+minimumExposure G D)
    (reserve : minimumExposure G D+1≤d)
    (exterior : r+2*(d+∑i,(m i-1)/2)≤s-matchingEdges (G.induce K.core))
    (esc : matchingEdges (G.induce K.core)<s)
    (loss : UnpaidHeight G K n m r j) (win : WinsHeight n m r j x y) (mixed : 2≤y) :
    x=2 ∧ (∑i,(n i-1)/2)<originalThresholdCount n 2 ∧
      (y=2 ∨ (y=m ⟨0,ht⟩ ∧ j=m ⟨0,ht⟩+1)) := by
  let μ := matchingEdges (G.induce K.core)
  let a := K.roots.ncard
  let ρ := minimumExposure G D
  have need := unpaid_height_missing_threshold G K n m r j hn hm pn esc loss x y win
  obtain ⟨nunit,_,limited,_⟩ := need
  change originalThresholdCount n x≤μ at limited
  obtain ⟨_,_,height,_,present,rect⟩ := win
  have short : a+2*μ<2*widthAt n m r j := by
    unfold UnpaidHeight at loss
    change a+2*μ+_+_<2*widthAt n m r j at loss;omega
  have bound := units_and_twos_below_mass m pm
  have mono := threshold_anti_height m mixed
  change (∑i,m i)+d≤μ+a+ρ at mass
  change a+r+2*(d+∑i,(n i-1)/2)≤t at endpoint
  change ρ+1≤d at reserve
  have many : (∑i,(n i-1)/2)<originalThresholdCount n x := by omega
  have xeq : x=2 := by
    by_contra ne
    have hi : 3≤x := by omega
    have no := half_extra_pays_large_threshold n hi
    omega
  subst x
  refine ⟨rfl,many,?_⟩
  by_cases two : y=2
  · exact Or.inl two
  right
  have high : 3≤y := by omega
  have bcap := (original_threshold_prefix m hm y ⟨0,ht⟩).2 present
  have cnt := half_extra_pays_large_threshold m high
  change r+2*(d+∑i,(m i-1)/2)≤s-μ at exterior
  change μ<s at esc
  have jnext : j=y+1 := by omega
  by_contra! bad
  have jfits : j≤m ⟨0,ht⟩ := by omega
  have qpos := (original_threshold_prefix m hm j ⟨0,ht⟩).1 jfits
  have one := original_threshold_one n pn
  have red : 0<originalThresholdCount n 1 := by omega
  have eq : 1+j-1=j := by omega
  have blue := actual_rectangle_le_column (r:=r) n m hn hm eq red qpos
  rw [one] at blue
  omega

#print axioms half_extra_pays_large_threshold
#print axioms units_and_twos_below_mass
#print axioms single_escape_unpaid_rectangle
end JSP452Audit.StarHost
