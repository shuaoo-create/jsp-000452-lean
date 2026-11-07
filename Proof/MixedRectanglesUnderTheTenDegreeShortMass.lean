import EndpointGuardsOnTheActualLongTenDegreeSide
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem mixed_rectangle_under_defect_mass {s t : ℕ} (a μ : ℕ) (W : RemovalBudget s)
    (fit : W.loss≤μ) (budgetLive : 0<W.len) (n : Fin s→ℕ) (m : Fin t→ℕ) (r d j x y : ℕ)
    (hs : 0<s) (ht : 0<t) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (endpoint : a+r+2*(d+∑i,(n i-1)/2)≤t)
    (mass : (∑i,m i)≤μ+a+1)
    (reserve : 1+1≤d)
    (exterior : r+2*(d+∑i,(m i-1)/2)≤s-μ)
    (esc : μ<s)
    (loss : a+2*μ+widthAt (W.entries n) m (r+a) j+widthAt (commonErasedDemand n W a μ) m r j<2*widthAt n m r j) (win : WinsHeight n m r j x y) (mixed : 2≤y) :
    x=2 ∧ (∑i,(n i-1)/2)<originalThresholdCount n 2 ∧
      (y=2 ∨ (y=m ⟨0,ht⟩ ∧ j=m ⟨0,ht⟩+1)) := by
  have need := missing_threshold_of_two_budget_columns n m hn hm pn W fit budgetLive loss x y win
  obtain ⟨nunit,_,limited,_⟩ := need
  change originalThresholdCount n x≤μ at limited
  obtain ⟨_,_,height,_,present,rect⟩ := win
  have short : a+2*μ<2*widthAt n m r j := by
    change a+2*μ+_+_<2*widthAt n m r j at loss;omega
  have bound := units_and_twos_below_mass m pm
  have mono := threshold_anti_height m mixed
  change a+r+2*(d+∑i,(n i-1)/2)≤t at endpoint
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

#print axioms mixed_rectangle_under_defect_mass
end JSP452Audit.StarHost
