import AllBinaryExact
import StrictNoIsolates
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- Entry into the still open high-degree branch. Both the strict source
and every subsequent comparison use the same universe of finite hosts. -/
theorem high_degree_source_of_failure {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m) ≠ ∑ k∈Finset.Icc 2 (s+t),diagonal n m k) :
    ∃ F : StrictFamily.{u}, let D := diagonal F.n F.m (F.r+2)-1
      AllSmallerPaid.{u} F.rank ∧ 3≤D ∧ 2≤F.rank ∧
      F.edges+1=rowEnergy F.n F.m F.r ∧ matchingEdges F.G<F.rank ∧
      (∀v,0<Nat.card (F.G.neighborSet v) ∧ Nat.card (F.G.neighborSet v)≤D) ∧
      (∃v,Nat.card (F.G.neighborSet v)=D) ∧
      1≤minimumExposure F.G D ∧
      ((D:ℤ)-2)*(minimumExposure F.G D:ℤ)+2 ≤ 2*((D/2:ℕ):ℤ)*(((D/2:ℕ):ℤ)+1) := by
  obtain ⟨F,paid,_,order⟩ := failure_has_smaller_rank_baseline.{u} hs ht n m hn hm pn pm fail
  obtain ⟨rank,ed,rankDef,cap,peak,_⟩ := minimal_rank_exact_source F paid
  have miss := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  exact ⟨F,paid,strict_source_degree_at_least_three F paid,rank,ed,rankDef,
    fun v => ⟨minimal_strict_no_isolates F order v,cap v⟩,peak,miss.1.trans miss.2,minimal_source_exposure_cap F paid⟩
#print axioms high_degree_source_of_failure
end JSP452Audit.StarHost