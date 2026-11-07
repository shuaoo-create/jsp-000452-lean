import ActualExteriorWholeTails
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Both the matching endpoint and the actual smaller-rank edge price
apply to the complete exterior row, on that same exterior graph. -/
theorem positive_exterior_row_price {X : Type u} [Finite X] (H:SimpleGraph X) {s t r N d : ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m)
    (pn:∀i,1≤n i) (pm:∀j,1≤m j) (row:ForcingRow H s t (padDemand n) (padDemand m) r)
    (paid:AllSmallerPaid.{u} N) (rank:rowCount s t r=matchingEdges H+d)
    (smaller:rowCount s t r<N) (pos:0<d) :
    rowEnergy n m r≤H.edgeSet.ncard ∧ r+d+1≤min s t ∧ max s t≤matchingEdges H := by
  refine ⟨paid hs ht n m hn hm pn pm H r row smaller,?_⟩
  have count : matchingEdges (⊥:SimpleGraph X)+matchingEdges (H \ ⊥)+d=rowCount s t r := by
    simpa only [matchingEdges_bot,sdiff_bot,Nat.zero_add] using rank.symm
  have k0 : matchingEdges (⊥:SimpleGraph X)<min s t := by rw [matchingEdges_bot];omega
  have price := forcing_row_strong_lengths_of_coloring H hs ht _ _ (pad_positive n pn) (pad_positive m pm)
    row ⊥ bot_le d pos count k0
  simpa only [matchingEdges_bot,sdiff_bot,Nat.zero_add] using price

/-- If either original list escapes, the row after actually deleting the
root labels and all core edges has rank k+d and gives the entire pair of
length endpoints on the exterior, as well as its paid row area. -/
theorem strict_exterior_whole_tail_prices (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let μ := matchingEdges (F.G.induce K.core)
    let a := K.roots.ncard
    let H := F.G.induce K.rest
    let k := matchingEdges H
    let d := F.rank-matchingEdges F.G
    (μ<F.s → rowCount (F.s-μ) F.t (F.r+a)=k+d ∧ rowCount (F.s-μ) F.t (F.r+a)<F.rank ∧
      rowEnergy (remainingDemand F.n μ) F.m (F.r+a)≤H.edgeSet.ncard ∧
      μ+a+F.r+d+1≤F.s ∧ a+F.r+d+1≤F.t ∧ max (F.s-μ) F.t≤k) ∧
    (μ<F.t → rowCount F.s (F.t-μ) (F.r+a)=k+d ∧ rowCount F.s (F.t-μ) (F.r+a)<F.rank ∧
      rowEnergy F.n (remainingDemand F.m μ) (F.r+a)≤H.edgeSet.ncard ∧
      μ+a+F.r+d+1≤F.t ∧ a+F.r+d+1≤F.s ∧ max F.s (F.t-μ)≤k) := by
  intro μ a H k d
  obtain ⟨_,_,less,_,_,_⟩ := minimal_rank_exact_source F paid
  have original : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have pos : 0<d := by dsimp [d];omega
  have split := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=a+μ+k at split
  obtain ⟨_,core,_,_⟩ := strict_source_paid_erased_core_successors F paid K
  have large := strict_source_degree_at_least_three F paid
  change diagonal F.n F.m (F.r+2)-1≤2*μ at core
  have progress : 0<μ := by omega
  have rank : a+μ+k+d=F.s+F.t-1-F.r := by change matchingEdges F.G+d=F.s+F.t-1-F.r at original;omega
  constructor
  · intro escaped
    have size : rowCount (F.s-μ) F.t (F.r+a)=k+d := by dsimp [rowCount];omega
    have strict : rowCount (F.s-μ) F.t (F.r+a)<F.rank := by omega
    have row := exterior_complete_red_tail F.G K F.n F.m F.hn F.hm F.pn F.pm F.row
    obtain ⟨price,low,high⟩ := positive_exterior_row_price H (by omega : 0<F.s-μ) F.ht
      (remainingDemand F.n μ) F.m (remainingDemand_antitone F.n F.hn _) F.hm (remainingDemand_positive F.n F.pn _)
      F.pm row paid size strict pos
    obtain ⟨left,right⟩ := le_min_iff.mp low
    exact ⟨size,strict,price,by omega,by omega,high⟩
  · intro escaped
    have size : rowCount F.s (F.t-μ) (F.r+a)=k+d := by dsimp [rowCount];omega
    have strict : rowCount F.s (F.t-μ) (F.r+a)<F.rank := by omega
    have row := exterior_complete_blue_tail F.G K F.n F.m F.hn F.hm F.pn F.pm F.row
    obtain ⟨price,low,high⟩ := positive_exterior_row_price H F.hs (by omega : 0<F.t-μ)
      F.n (remainingDemand F.m μ) F.hn (remainingDemand_antitone F.m F.hm _) F.pn (remainingDemand_positive F.m F.pm _)
      row paid size strict pos
    obtain ⟨left,right⟩ := le_min_iff.mp low
    exact ⟨size,strict,price,by omega,by omega,high⟩

#print axioms positive_exterior_row_price
#print axioms strict_exterior_whole_tail_prices
end JSP452Audit.StarHost
