import StrictFullHeadOnlySix
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Whenever the degree is greater than six, both original heads are strictly below
the cap and both lists must escape in every actual ordinary region. -/
theorem strict_from_seven_double_escape (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    7≤D → (∀i,F.n i<D) ∧ (∀j,F.m j<D) ∧ μ+K.roots.ncard+F.r+d+1≤min F.s F.t ∧
      max F.s F.t≤matchingEdges (F.G.induce K.rest) := by
  intro D μ d large
  have no := strict_full_head_only_six F paid K
  obtain ⟨nr,mb⟩ := minimal_original_head_cap F paid
  have red : F.n ⟨0,F.hs⟩<D := by
    have cap := nr ⟨0,F.hs⟩
    by_contra! bad
    have high := no (Or.inl (by change F.n ⟨0,F.hs⟩=D;omega))
    change D=6 at high;omega
  have blue : F.m ⟨0,F.ht⟩<D := by
    have cap := mb ⟨0,F.ht⟩
    by_contra! bad
    have high := no (Or.inr (by change F.m ⟨0,F.ht⟩=D;omega))
    change D=6 at high;omega
  have escape := strict_subcap_heads_force_double_escape F paid K red blue
  obtain ⟨len,ex,r,b,_⟩ := strict_double_escape_data F paid K escape
  exact ⟨r,b,len,ex⟩

def FromSevenDoubleEscapes (F : StrictFamily.{u}) : Prop :=
  let D := diagonal F.n F.m (F.r+2)-1
  7≤D → ∀K:DegreeRegion F.G D, (∀i,F.n i<D) ∧ (∀j,F.m j<D) ∧
    matchingEdges (F.G.induce K.core)+K.roots.ncard+F.r+(F.rank-matchingEdges F.G)+1≤min F.s F.t ∧
    max F.s F.t≤matchingEdges (F.G.induce K.rest)

theorem original_failure_from_seven_double_escape {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u}, AllSmallerPaid.{u} F.rank ∧ 6≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      RemainingOriginalRegimes F ∧ NonunitOnFullHeads F ∧ GapThreeOnFullHeads F ∧ HalfBoundOnFullHeads F ∧
      FromSevenDoubleEscapes F := by
  obtain ⟨F,paid,deg,edges,order,types,real,gap,half⟩ := original_failure_full_opposite_at_most_half.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,deg,edges,order,types,real,gap,half,fun large K => strict_from_seven_double_escape F paid K large⟩

#print axioms strict_from_seven_double_escape
#print axioms original_failure_from_seven_double_escape
end JSP452Audit.StarHost