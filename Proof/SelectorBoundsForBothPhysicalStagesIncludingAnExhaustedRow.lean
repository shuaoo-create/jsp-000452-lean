import ActualWidthPricesForTheUniqueRegularBlockAtTheThreeTopNonpeakHeights
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem exposure_zero_below_edge_count {X:Type u} [Finite X] (G:SimpleGraph X) (q:ℕ) (few:G.edgeSet.ncard<q) :
    minimumExposure G q=0 := by
  obtain ⟨M,_,_,att⟩ := minimumExposure_attained G q
  have empty : exposedFull G M q=∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro v mem
    have deg := mem.2
    have ind : G.IsIndepSet {v} := by
      intro x hx y hy ne
      exact (ne ((Set.mem_singleton_iff.mp hx).trans (Set.mem_singleton_iff.mp hy).symm)).elim
    have cost := JSP452Audit.StarHost.degree_on_independent_full_set G {v} q (by intro w hw;rw [Set.mem_singleton_iff.mp hw];exact deg) ind
    rw [Set.ncard_singleton,Nat.mul_one] at cost;omega
  rw [empty,Set.ncard_empty] at att;exact att.symm

theorem exposure_budget_even_if_exhausted {X:Type u} [Finite X] (G:SimpleGraph X) {s t r N q a:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀j,1≤n j) (pm:∀j,1≤m j)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (cap:∀v,Nat.card (G.neighborSet v)≤q) (small:a<q) (net:G.edgeSet.ncard≤rowEnergy n m r+a) :
    ((q:ℤ)-2)*minimumExposure G q≤2*((q/2:ℕ):ℤ)*(((q/2:ℕ):ℤ)+1)+2*a := by
  by_cases live:0<rowCount s t r
  · have height := live_row_height_at_degree_cap G hs ht n m hn hm pn pm row live cap
    have budget := smaller_row_exposure_budget hs ht n m hn hm pn pm G r q N (by omega) row live smaller paid cap height
    omega
  · have empty : rowEnergy n m r=0 := by simp only [rowEnergy,show rowCount s t r=0 by omega,Finset.range_zero,Finset.sum_empty]
    rw [exposure_zero_below_edge_count G q (by omega),Nat.cast_zero,mul_zero]
    positivity

theorem odd_stage_zero_surplus {X:Type u} [Finite X] (G:SimpleGraph X) {s t r N p:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀j,1≤n j) (pm:∀j,1≤m j)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (cap:∀v,Nat.card (G.neighborSet v)≤2*p-1) (many:6≤p) (net:G.edgeSet.ncard≤rowEnergy n m r) :
    minimumExposure G (2*p-1)≤p := by
  have lim := exposure_budget_even_if_exhausted G hs ht n m hn hm pn pm row smaller paid cap
    (show 0<2*p-1 by omega) (by simpa using net)
  rw [show (2*p-1)/2=p-1 by omega] at lim
  push_cast [Nat.cast_sub (by omega : 1≤p),Nat.cast_sub (by omega : 1≤2*p)] at lim
  by_contra! high
  have inc := mul_nonneg (show (0:ℤ)≤2*(p:ℤ)-3 by omega) (show (0:ℤ)≤(minimumExposure G (2*p-1):ℤ)-p-1 by omega)
  linarith only [inc,lim,show (6:ℤ)≤p by exact_mod_cast many]

theorem even_stage_low_surplus {X:Type u} [Finite X] (G:SimpleGraph X) {s t r N p:ℕ}
    (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ) (hn:Antitone n) (hm:Antitone m) (pn:∀j,1≤n j) (pm:∀j,1≤m j)
    (row:ForcingRow G s t (padDemand n) (padDemand m) r) (smaller:rowCount s t r<N) (paid:AllSmallerPaid.{u} N)
    (cap:∀v,Nat.card (G.neighborSet v)≤2*p-2) (many:6≤p) (net:G.edgeSet.ncard≤rowEnergy n m r+(p-2)) :
    minimumExposure G (2*p-2)≤p+2 := by
  have lim := exposure_budget_even_if_exhausted G hs ht n m hn hm pn pm row smaller paid cap (show p-2<2*p-2 by omega) net
  rw [show (2*p-2)/2=p-1 by omega] at lim
  push_cast [Nat.cast_sub (by omega : 1≤p),Nat.cast_sub (by omega : 2≤2*p),Nat.cast_sub (by omega : 2≤p)] at lim
  by_contra! high
  have inc := mul_nonneg (show (0:ℤ)≤2*(p:ℤ)-4 by omega) (show (0:ℤ)≤(minimumExposure G (2*p-2):ℤ)-p-3 by omega)
  linarith only [inc,lim,show (6:ℤ)≤p by exact_mod_cast many]

#print axioms exposure_zero_below_edge_count
#print axioms exposure_budget_even_if_exhausted
#print axioms odd_stage_zero_surplus
#print axioms even_stage_low_surplus
end JSP452Audit.StarHost
