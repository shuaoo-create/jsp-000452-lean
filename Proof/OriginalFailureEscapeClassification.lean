import ActualEscapePriceGaps
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Degree and length classification on each individual region, with both
strict successor gaps for every escaping color. -/
def RemainingRegionCases (F : StrictFamily.{u})
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  let μ := matchingEdges (F.G.induce K.core)
  let k := matchingEdges (F.G.induce K.rest)
  let a := K.roots.ncard
  let d := F.rank-matchingEdges F.G
  let E := rowEnergy F.n F.m F.r
  μ+d < max F.s F.t ∧
  (μ<F.s → EscapePriceGap F.G K F.n F.m F.r E) ∧
  (μ<F.t → EscapePriceGap F.G K F.m F.n F.r E) ∧
  ((F.t≤μ ∧ μ+a+F.r+d+1≤F.s ∧ max (F.s-μ) F.t≤k ∧ (∀j,F.m j<D)) ∨
   (F.s≤μ ∧ μ+a+F.r+d+1≤F.t ∧ max F.s (F.t-μ)≤k ∧ (∀i,F.n i<D)) ∨
   (6≤D ∧ μ+a+F.r+d+1≤min F.s F.t ∧ max F.s F.t≤k ∧ (∀i,F.n i<D) ∧ (∀j,F.m j<D)))

theorem strict_remaining_region_cases (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) : RemainingRegionCases F K := by
  let μ := matchingEdges (F.G.induce K.core)
  let d := F.rank-matchingEdges F.G
  have escape := strict_source_one_list_escapes F paid K
  change μ+d<max F.s F.t at escape
  have prices := strict_same_region_escape_prices F paid K
  have actual := strict_exterior_whole_tail_prices F paid K
  have sides := single_embedded_side_heads_below_degree F paid K
  refine ⟨escape,prices.1,prices.2,?_⟩
  by_cases b : F.t≤μ
  · have e : μ<F.s := by omega
    obtain ⟨_,_,_,length,_,rank⟩ := actual.1 e
    exact Or.inl ⟨b,length,rank,sides.2 b e⟩
  by_cases a : F.s≤μ
  · have e : μ<F.t := by omega
    obtain ⟨_,_,_,length,_,rank⟩ := actual.2 e
    exact Or.inr (Or.inl ⟨a,length,rank,sides.1 a e⟩)
  obtain ⟨length,rank,n,m,high⟩ := strict_double_escape_data F paid K
    (by change μ<min F.s F.t;omega)
  exact Or.inr (Or.inr ⟨high,length,rank,n,m⟩)

/-- The least failure of the original equation has only these three
remaining regional cases. All assertions concern the same graph. -/
theorem original_failure_has_classified_regions {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      ∀K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1), RemainingRegionCases F K := by
  obtain ⟨F,paid,edges,order⟩ := failure_has_smaller_rank_baseline.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,edges,order,strict_remaining_region_cases F paid⟩

#print axioms strict_remaining_region_cases
#print axioms original_failure_has_classified_regions
end JSP452Audit.StarHost
