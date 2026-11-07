import StrictFullHeadExcludedAllDegrees
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

def OnlyDoubleEscape (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  (∀i,F.n i<D) ∧ (∀j,F.m j<D) ∧
    (∀K:DegreeRegion F.G D,
      matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧
      max F.s F.t≤matchingEdges (F.G.induce K.rest))

theorem strict_only_double_escape (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    OnlyDoubleEscape F := by
  unfold OnlyDoubleEscape
  intro D
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have absent := strict_full_head_impossible F paid K
  have red : F.n ⟨0,F.hs⟩<D := by
    have cap := nc ⟨0,F.hs⟩
    by_contra! hi;exact absent (Or.inl (by change F.n ⟨0,F.hs⟩=D;omega))
  have blue : F.m ⟨0,F.ht⟩<D := by
    have cap := mc ⟨0,F.ht⟩
    by_contra! hi;exact absent (Or.inr (by change F.m ⟨0,F.ht⟩=D;omega))
  refine ⟨fun i => (F.hn (show (⟨0,F.hs⟩ : Fin F.s)≤ i from Nat.zero_le _)).trans_lt red,
    fun j => (F.hm (show (⟨0,F.ht⟩ : Fin F.t)≤j from Nat.zero_le _)).trans_lt blue,?_⟩
  intro region
  have both := strict_subcap_heads_force_double_escape F paid region red blue
  obtain ⟨len,ext,_,_,_⟩ := strict_double_escape_data F paid region both
  exact ⟨len,ext⟩

theorem original_failure_only_double_escape {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧ OnlyDoubleEscape F := by
  obtain ⟨F,paid,deg,edges,order,_⟩ := original_failure_needs_degree_six.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,strict_only_double_escape F paid⟩

#print axioms strict_only_double_escape
#print axioms original_failure_only_double_escape
end JSP452Audit.StarHost