import TwoLongListsImpossibleAtDegreeNine
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem original_failure_nine_single_short {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F : StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧
      (∀B : StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B : StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      OnlyDoubleEscape F ∧
      (10≤diagonal F.n F.m (F.r+2)-1 ∨
        (diagonal F.n F.m (F.r+2)-1=9 ∧ Nonempty (NinePortRegion F.G) ∧
        ∀R : NinePortRegion F.G,let P := R.totalCapacity
          (F.s+5≤P ∧ P+F.r+10≤F.t) ∨ (F.t+5≤P ∧ P+F.r+10≤F.s))) := by
  obtain ⟨F,paid,lower,edge,order,regime⟩ := original_failure_needs_degree_nine.{u} hs ht n m hn hm pn pm fail
  refine ⟨F,paid,edge,order,regime,?_⟩
  by_cases high : 10≤diagonal F.n F.m (F.r+2)-1
  · exact Or.inl high
  · have nine : diagonal F.n F.m (F.r+2)-1=9 := by omega
    obtain ⟨R,_⟩ := strict_nine_port_region_exists F paid nine
    exact Or.inr ⟨nine,⟨R⟩,strict_nine_exactly_one_short_list F paid nine⟩

#print axioms original_failure_nine_single_short
end JSP452Audit.StarHost
