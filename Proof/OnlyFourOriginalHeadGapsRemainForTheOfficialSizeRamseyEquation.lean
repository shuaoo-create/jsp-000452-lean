import TheFifthGapIsImpossibleForEveryOriginalStrictSource
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem original_failure_has_one_of_four_gaps {s t:ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail:sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ OnlyDoubleEscape F ∧ ActualPeakObstruction F ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      let D := diagonal F.n F.m (F.r+2)-1
      let gap := D-max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)
      11≤D ∧ 1≤gap ∧ gap≤4 ∧ gap+2≤min (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩) ∧ 2*gap+2≤D := by
  obtain ⟨F,paid,deg,edges,order,both⟩ := original_failure_needs_degree_eleven hs ht n m hn hm pn pm fail
  obtain ⟨pos,_,heads,cap⟩ := strict_double_head_gap_range F paid
  exact ⟨F,paid,both,strict_actual_peak_factor_obstruction F paid,edges,order,deg,pos,strict_original_head_gap_at_most_four F paid,heads,cap⟩

#print axioms original_failure_has_one_of_four_gaps
end JSP452Audit.StarHost
