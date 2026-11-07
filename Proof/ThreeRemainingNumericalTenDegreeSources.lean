import ExcludeTheActualSingleAndDoubleRegularSources
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem strict_ten_remaining_width_counts (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) :
    let h := highestWidth F.n F.m F.r
    let c := (oddRegularComponents F.G 10).ncard
    let rho := minimumExposure F.G 10
    (h=1 ∧ c=0 ∧ rho=3) ∨ (h=2 ∧ c=1 ∧ rho=4) ∨ (h=6 ∧ c=6 ∧ rho=6) := by
  classical
  intro h c rho
  let Z := oddRegularComponents F.G 10
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  have up : h≤rho := (strict_ten_inventory F paid ten).2.1
  have lim : rho≤6 := (strict_ten_inventory F paid ten).2.2.2.1
  by_cases none:c=0
  · obtain ⟨hh,rr,_⟩ := strict_ten_zero_odd_requires_score_one F paid ten none
    exact Or.inl ⟨hh,none,rr⟩
  by_cases single:c=1
  · have wide : c<h := by
      by_contra! low
      have one : highestWidth F.n F.m F.r=1 := by change h=1;omega
      obtain ⟨C,mem⟩ := (Set.ncard_pos (Set.toFinite Z)).mp (show 0<c by omega)
      have odd := (show C∈oddRegularComponents F.G 10 from mem).1
      obtain ⟨j,ord⟩ := odd
      have size := matching_edges_fit_order C.toSimpleGraph
      change 2*matchingEdges C.toSimpleGraph≤Nat.card C.supp at size
      exact strict_ten_one_imperfect_at_width_one_impossible F paid ten one C mem.2 (by omega)
    obtain ⟨_,narrow,extra,limit,_⟩ := strict_ten_excess_width_cut F paid ten wide
    change h≤2 at narrow
    change h+2≤rho at extra
    change rho≤4 at limit
    exact Or.inr (Or.inl ⟨by omega,single,by omega⟩)
  · have big : 5<h := by
      by_contra! low
      have count : 2≤Z.toFinite.toFinset.card := by rw [←Set.ncard_coe_finset,Z.toFinite.coe_toFinset];change 2≤c;omega
      obtain ⟨T,sub,num⟩ := Finset.exists_subset_card_eq count
      exact strict_ten_two_odd_components_at_small_width_impossible F paid ten low T num
        (fun i mem => Z.toFinite.mem_toFinset.mp (sub mem))
    have six : rho=6 := by omega
    have eq := ((strict_ten_cut_inventory F paid ten).2.1 six).1
    exact Or.inr (Or.inr ⟨by omega,eq,six⟩)
#print axioms strict_ten_remaining_width_counts
end JSP452Audit.StarHost
