import FiveEmbeddedSubcapPrice
import StrictDoubleEmbeddingFromSix
namespace JSP452Audit.StarHost
universe u

/-- In degree five, whichever of the two actual embedded lists is shorter
must have a five-leaf head. In a tie the assertion applies in both colors. -/
theorem five_embedded_shorter_head_attains (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (five : diagonal F.n F.m (F.r+2)-1=5)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    (F.s≤F.t → F.n ⟨0,F.hs⟩=5) ∧ (F.t≤F.s → F.m ⟨0,F.ht⟩=5) := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨hs,ht⟩ := max_le_iff.mp both
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have strict := F.strict
  have mass := strict_source_whole_list_alternatives F K
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  obtain ⟨one,width⟩ := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have deficit := (minimal_strict_source_deficit F paid).2.1
  have costs := ((low_degree_original_costs F paid K).2.2 five).2.1
  change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
    crossCount F.G K.roots K.rest)≤10 at costs
  have slack : 3*minimumExposure F.G D+rootShortfall F.G K.roots D≤10 := by omega
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨nmax,mmax⟩ := minimal_original_head_cap F paid
  constructor
  · intro ord
    by_contra unequal
    have bound := nmax ⟨0,F.hs⟩
    have neq : F.n ⟨0,F.hs⟩<D := by dsimp [D];omega
    have p := five_shorter_subcap_paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K five ord
      (by omega) neq top cap width (one.trans width) d balance deficit ht mass.1 mass.2 slack
    omega
  · intro ord
    by_contra unequal
    have bound := mmax ⟨0,F.ht⟩
    have neq : F.m ⟨0,F.ht⟩<D := by dsimp [D];omega
    have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipWidth := (highest_width_colour_swap F.m F.n F.r).le.trans width
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r :=
      by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have p := five_shorter_subcap_paid F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K five ord
      (by omega) neq flipTop cap flipWidth (one.trans width) d flipRank deficit hs mass.2 mass.1 slack
    rw [row_energy_colour_swap F.m F.n] at p;omega

#print axioms five_embedded_shorter_head_attains
end JSP452Audit.StarHost
