import ComplementaryPaletteForTheShortList
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_nine_capacity_window (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (nine : diagonal F.n F.m (F.r+2)-1=9) (R : NinePortRegion F.G) :
    let P := R.totalCapacity
    let d := F.rank-matchingEdges F.G
    (F.s≤P → F.s+d+2*(∑i,(F.n i-1)/2)≤P+1) ∧
    (P<F.s → P+F.r+2*(d+∑j,(F.m j-1)/2)≤F.s) ∧
    (F.t≤P → F.t+d+2*(∑j,(F.m j-1)/2)≤P+1) ∧
    (P<F.t → P+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t) ∧
    (F.s+5≤P ∨ P+F.r+10≤F.s) ∧ (F.t+5≤P ∨ P+F.r+10≤F.t) := by
  intro P d
  have below := (minimal_rank_exact_source F paid).2.2.1
  have ⟨_,_,many,_,i,j,_,_,_,pair,_⟩ := strict_nine_original_peak F paid nine
  have gap := (minimal_strict_source_deficit F paid).2.1
  rw [nine] at gap
  have hp := (strict_nine_original_peak F paid nine).1
  have four : 4≤d := by change minimumExposure F.G 9+1≤F.rank-matchingEdges F.G at gap;dsimp [d];omega
  have n4 : 4≤F.n i := by rcases pair with ⟨h,_⟩|⟨h,_⟩ <;> omega
  have m4 : 4≤F.m j := by rcases pair with ⟨_,h⟩|⟨_,h⟩ <;> omega
  have rn := Finset.single_le_sum (f:=fun z => (F.n z-1)/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have bm := Finset.single_le_sum (f:=fun z => (F.m z-1)/2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have nw : 1≤∑i,(F.n i-1)/2 := by omega
  have mw : 1≤∑j,(F.m j-1)/2 := by omega
  obtain ⟨ns,ms⟩ := strict_nine_short_adapted_endpoints F paid R
  obtain ⟨ml,nl⟩ := strict_nine_actual_erased_endpoints F paid R
  have shortS (le : F.s≤P) : F.s+d+2*(∑i,(F.n i-1)/2)≤P+1 := (ns le).2
  have shortT (le : F.t≤P) : F.t+d+2*(∑j,(F.m j-1)/2)≤P+1 := (ms le).2
  have longS (gt : P<F.s) : P+F.r+2*(d+∑j,(F.m j-1)/2)≤F.s := by
    obtain ⟨pos,_,_,_,fee⟩ := nl gt
    change d+1≤F.s-F.r-P at pos
    change 2*(d+∑j,(F.m j-1)/2)≤F.s-F.r-P at fee
    omega
  have longT (gt : P<F.t) : P+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t := by
    obtain ⟨pos,_,_,_,fee⟩ := ml gt
    change d+1≤F.t-F.r-P at pos
    change 2*(d+∑i,(F.n i-1)/2)≤F.t-F.r-P at fee
    omega
  refine ⟨shortS,longS,shortT,longT,?_,?_⟩
  · by_cases le : F.s≤P
    · have := shortS le;exact Or.inl (by omega)
    · have := longS (by omega);exact Or.inr (by omega)
  · by_cases le : F.t≤P
    · have := shortT le;exact Or.inl (by omega)
    · have := longT (by omega);exact Or.inr (by omega)

#print axioms strict_nine_capacity_window
end JSP452Audit.StarHost
