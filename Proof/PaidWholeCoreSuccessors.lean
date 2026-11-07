import OrdinaryRegionLargePiece
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Exact-source baseline and edge charge for one complete shifted list pair. -/
def PaidErasedCoreRow {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X) {s t : ℕ}
    (n : Fin s→ℕ) (m : Fin t→ℕ) (r N d : ℕ) : Prop :=
  let Z := eraseInternal G A
  let μ := matchingEdges (G.induce A)
  ForcingRow Z s t (padDemand n) (padDemand m) r ∧
  rowCount s t r+μ=N ∧ rowCount s t r=matchingEdges Z+d ∧
  0<rowCount s t r ∧ rowCount s t r<N ∧
  rowEnergy n m r≤Z.edgeSet.ncard ∧ rowEnergy n m r+(G.induce A).edgeSet.ncard≤G.edgeSet.ncard

private theorem pay_erased_core_row {X : Type u} [Finite X] (G : SimpleGraph X) (A : Set X)
    {s t : ℕ} (hs : 0<s) (ht : 0<t) (n : Fin s→ℕ) (m : Fin t→ℕ)
    (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (r N d : ℕ) (paid : AllSmallerPaid.{u} N)
    (row : ForcingRow (eraseInternal G A) s t (padDemand n) (padDemand m) r)
    (size : rowCount s t r+matchingEdges (G.induce A)=N)
    (balance : matchingEdges (eraseInternal G A)+d+matchingEdges (G.induce A)=N)
    (dpos : 0<d) (progress : 0<matchingEdges (G.induce A)) :
    PaidErasedCoreRow G A n m r N d := by
  have cheaper := paid hs ht n m hn hm pn pm _ r row (by omega)
  have fee := erase_internal_edge_count G A
  exact ⟨row,size,by omega,by omega,by omega,cheaper,by omega⟩

theorem strict_source_paid_erased_core_successors (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (∃c:(F.G.induce K.core).ConnectedComponent,D+1≤Nat.card c.supp) ∧ D≤2*μ ∧
    (μ<F.t → PaidErasedCoreRow F.G K.core F.n (remainingDemand F.m μ) F.r F.rank d) ∧
    (μ<F.s → PaidErasedCoreRow F.G K.core (remainingDemand F.n μ) F.m F.r F.rank d) := by
  intro D μ d
  obtain ⟨_,_,below,cap,_,_⟩ := minimal_rank_exact_source F paid
  have large : 3≤D := strict_source_degree_at_least_three F paid
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have exp : 0<minimumExposure F.G D := lt_of_lt_of_le (by omega : 0<highestWidth F.n F.m F.r) width.2
  obtain ⟨long,low⟩ := ordinary_region_has_large_piece F.G D (by omega) cap exp K
  change D≤2*μ at low
  have progress : 0<μ := by omega
  have pos : 0<d := by dsimp [d];omega
  have orig : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have split := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=K.roots.ncard+μ+matchingEdges (F.G.induce K.rest) at split
  have actual := whole_core_erasure_exact_rank F.G K
  have balance : matchingEdges (eraseInternal F.G K.core)+d+μ=F.rank := by omega
  refine ⟨long,low,?_,?_⟩
  · intro live
    have row := erase_core_complete_blue_row F.G K F.n F.m F.hm F.row
    apply pay_erased_core_row F.G K.core F.hs (by omega) F.n (remainingDemand F.m μ)
      F.hn (remainingDemand_antitone F.m F.hm μ) F.pn (remainingDemand_positive F.m F.pm μ)
      F.r F.rank d paid row _ balance pos progress
    change rowCount F.s (F.t-μ) F.r+μ=F.rank
    dsimp [StrictFamily.rank,rowCount] at orig ⊢;omega
  · intro live
    have row := erase_core_complete_red_row F.G K F.n F.m F.hn F.row
    apply pay_erased_core_row F.G K.core (by omega) F.ht (remainingDemand F.n μ) F.m
      (remainingDemand_antitone F.n F.hn μ) F.hm (remainingDemand_positive F.n F.pn μ) F.pm
      F.r F.rank d paid row _ balance pos progress
    change rowCount (F.s-μ) F.t F.r+μ=F.rank
    dsimp [StrictFamily.rank,rowCount] at orig ⊢;omega

#print axioms strict_source_paid_erased_core_successors
end JSP452Audit.StarHost
