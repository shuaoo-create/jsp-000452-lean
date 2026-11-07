import DoubleEmbeddedEdgePrice
namespace JSP452Audit.StarHost
universe u

/-- In a degree at least six strict source with both original lists embedded,
the shorter side must attain D. Both implications use the same F and K. -/
theorem double_embedded_shorter_head_must_attain (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (six : 6≤diagonal F.n F.m (F.r+2)-1) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    max F.s F.t≤μ+d →
      (F.s≤F.t → F.n ⟨0,F.hs⟩=D) ∧ (F.t≤F.s → F.m ⟨0,F.ht⟩=D) := by
  intro D μ d trigger
  have sections := strict_source_whole_list_alternatives F K
  have gap := strict_source_whole_list_gap F K
  obtain ⟨_,_,rankLess,cap,_,_⟩ := minimal_rank_exact_source F paid
  have strict := F.strict
  have pos : 0<d := by dsimp [d];omega
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  obtain ⟨activeRed,activeBlue⟩ := max_le_iff.mp trigger
  have sIn : F.s≤μ := by
    rcases gap.1 with small|big
    · change μ+d+1≤F.s at small;omega
    · change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at big;omega
  have tIn : F.t≤μ := by
    rcases gap.2 with small|big
    · change μ+d+1≤F.t at small;omega
    · change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at big;omega
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  obtain ⟨sr,tr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨cN,cM⟩ := minimal_original_head_cap F paid
  constructor
  · intro order
    have size : F.n ⟨0,F.hs⟩≤D := cN _
    by_contra ne
    have yes := double_embedded_profile_exclusion F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K order
      (by omega) (by omega : F.n ⟨0,F.hs⟩<D) top six cap width d balance sections.1 sections.2 tIn
    omega
  · intro order
    have size : F.m ⟨0,F.ht⟩≤D := cM _
    by_contra ne
    have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipWidth := (highest_width_colour_swap F.m F.n F.r).le.trans width
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have yes := double_embedded_profile_exclusion F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K order
      (by omega) (by omega : F.m ⟨0,F.ht⟩<D) flipTop six cap flipWidth d flipRank sections.2 sections.1 sIn
    rw [row_energy_colour_swap F.m F.n] at yes;omega

#print axioms double_embedded_shorter_head_must_attain
end JSP452Audit.StarHost
