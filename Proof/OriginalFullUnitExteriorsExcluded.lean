import StrictFullHeadNonunitExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def NonunitOnFullHeads (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  ∀K:DegreeRegion F.G D, let H := F.G.induce K.core
    (F.n ⟨0,F.hs⟩=D → 0<originalThresholdCount ((componentBudget H F.n).entries F.n) 2) ∧
    (F.m ⟨0,F.ht⟩=D → 0<originalThresholdCount ((componentBudget H F.m).entries F.m) 2)

theorem original_failure_needs_nonunit_full_exteriors {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      RemainingOriginalRegimes F ∧ NonunitOnFullHeads F := by
  obtain ⟨F,paid,deg,edges,order,types⟩ := original_failure_needs_degree_six.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,types,fun K => strict_full_head_nonunit_exterior F paid K⟩

#print axioms original_failure_needs_nonunit_full_exteriors
end JSP452Audit.StarHost