import GlobalStrictFamily
import CapacityMenuRow
namespace JSP452Audit.StarHost
open SimpleGraph
universe u
/-- Lower bounds apply even when a successor uses different lists, labels
and host. Empty rows have zero energy and need no forcing convention. -/
def AllSmallerPaid (N : ℕ) : Prop :=
  ∀ {X : Type u} [Finite X] {s t : ℕ} (_hs : 0<s) (_ht : 0<t) (n : Fin s → ℕ) (m : Fin t → ℕ),
    Antitone n → Antitone m → (∀ i, 1≤n i) → (∀ j, 1≤m j) →
    ∀ (G : SimpleGraph X) (r : ℕ), ForcingRow G s t (padDemand n) (padDemand m) r →
      rowCount s t r<N → rowEnergy n m r ≤ G.edgeSet.ncard

theorem smaller_paid_of_min_rank (F : StrictFamily.{u}) (low : ∀ B : StrictFamily.{u}, F.rank≤B.rank) :
    AllSmallerPaid.{u} F.rank := by
  intro X inst s t hs ht n m hn hm pn pm G r row smaller
  by_contra! bad
  have live : 0<rowCount s t r := by
    by_contra! zero
    have z : rowCount s t r=0 := by omega
    simp [rowEnergy,z] at bad
  let B : StrictFamily.{u} := ⟨X,G,s,t,r,n,m,hs,ht,hn,hm,pn,pm,live,row,bad⟩
  exact smaller.not_ge (low B)

theorem minimal_rank_exact_source (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    2≤F.rank ∧ F.G.edgeSet.ncard+1=rowEnergy F.n F.m F.r ∧ matchingEdges F.G<F.rank ∧
    (∀ v, Nat.card (F.G.neighborSet v) ≤ diagonal F.n F.m (F.r+2)-1) ∧
    (∃ v, Nat.card (F.G.neighborSet v) = diagonal F.n F.m (F.r+2)-1) ∧
    ∀ (i : Fin F.s) (j : Fin F.t), i.val+j.val=F.r →
      diagonal F.n F.m (F.r+2)=F.n i+F.m j-1 → 2≤F.n i ∧ 2≤F.m j := by
  apply strict_local_normal F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  intro v
  have child := row_delete_one F.G v _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) F.row
  apply paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm _ _ child
  have live := F.live
  rw [rowCount_succ]; change rowCount F.s F.t F.r - 1 < rowCount F.s F.t F.r
  omega

theorem failure_has_smaller_rank_baseline {s t : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s → ℕ) (m : Fin t → ℕ) (hn : Antitone n) (hm : Antitone m)
    (pn : ∀ i, 1≤n i) (pm : ∀ j, 1≤m j)
    (fail : sizeRamsey (forest n) (forest m) ≠ ∑ k ∈ Finset.Icc 2 (s+t), diagonal n m k) :
    ∃ F : StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → F.edges≤B.edges) ∧
      (∀ B : StrictFamily.{u}, B.rank=F.rank → B.edges=F.edges → F.order≤B.order) := by
  obtain ⟨start⟩ := strictFamily_of_failure.{u} hs ht n m hn hm pn pm fail
  obtain ⟨F,lo,edges,order⟩ := exists_global_minimal_strict start
  exact ⟨F,smaller_paid_of_min_rank F lo,edges,order⟩
#print axioms smaller_paid_of_min_rank
#print axioms minimal_rank_exact_source
#print axioms failure_has_smaller_rank_baseline
end JSP452Audit.StarHost