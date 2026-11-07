import StrictFullOppositeAtMostHalf
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def HalfBoundOnFullHeads (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  (F.n ⟨0,F.hs⟩=D → 2*F.m ⟨0,F.ht⟩≤D) ∧ (F.m ⟨0,F.ht⟩=D → 2*F.n ⟨0,F.hs⟩≤D)

theorem original_failure_full_opposite_at_most_half {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      RemainingOriginalRegimes F ∧ NonunitOnFullHeads F ∧ GapThreeOnFullHeads F ∧ HalfBoundOnFullHeads F := by
  obtain ⟨F,paid,deg,edges,order,types,real,gap⟩ := original_failure_needs_gap_three.{u} hs ht n m hn hm pn pm fail
  obtain ⟨K⟩ := degreeRegion_exists F.G (diagonal F.n F.m (F.r+2)-1)
  exact ⟨F,paid,deg,edges,order,types,real,gap,strict_full_opposite_at_most_half F paid K⟩

#print axioms original_failure_full_opposite_at_most_half
end JSP452Audit.StarHost