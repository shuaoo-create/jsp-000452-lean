import TwoEscapesCannotBothLoseAtTwo
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Local failure of the frozen original identity forces each escaping
color to lose one actual interior height; every winning pair there lacks
its escaping-side threshold in the retained-root successor. -/
theorem original_failure_has_missing_thresholds {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 4≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      ∀K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1),
        let μ := matchingEdges (F.G.induce K.core)
        RemainingRegionCases F K ∧ (μ<F.s → MissingHeightWitness F.G K F.n F.m F.r) ∧
          (μ<F.t → MissingHeightWitness F.G K F.m F.n F.r) := by
  obtain ⟨F,paid,deg,edges,order,regions⟩ := original_failure_needs_degree_four.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,fun K => ⟨regions K,strict_source_missing_heights F paid K⟩⟩

#print axioms original_failure_has_missing_thresholds
end JSP452Audit.StarHost
