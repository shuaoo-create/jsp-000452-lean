import LargeEmbeddedFullHeadPrice
namespace JSP452Audit.StarHost
universe u

/-- A strict smaller-rank counterexample with degree at least eight
cannot embed both of its original lists in any one ordinary core. -/
theorem large_strict_source_one_list_escapes (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (eight : 8≤diagonal F.n F.m (F.r+2)-1) :
    matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)<max F.s F.t := by
  let D := diagonal F.n F.m (F.r+2)-1
  let μ := matchingEdges (F.G.induce K.core)
  let d := F.rank-matchingEdges F.G
  by_contra! both
  have heads := double_embedded_shorter_head_must_attain F paid K (by omega) both
  have mass := strict_source_whole_list_alternatives F K
  have gap := strict_source_whole_list_gap F K
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have strict := F.strict
  have pos : 0<d := by dsimp [d];omega
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  have sIn : F.s≤μ := by
    rcases gap.1 with small|big
    · change μ+d+1≤F.s at small;change F.s≤μ+d at sr;omega
    · change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at big;omega
  have tIn : F.t≤μ := by
    rcases gap.2 with small|big
    · change μ+d+1≤F.t at small;change F.t≤μ+d at tr;omega
    · change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at big;omega
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  obtain ⟨inN,inM⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  rcases le_total F.s F.t with ord|ord
  · have p := large_embedded_full_head_paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K ord
      (by omega) (heads.1 ord) top eight cap width F.row d mass.1 mass.2 tIn
    omega
  · have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipWidth := (highest_width_colour_swap F.m F.n F.r).le.trans width
    have flipRow := swap_positive_forcing_row F.G (padDemand F.n) (padDemand F.m) F.row
    have p := large_embedded_full_head_paid F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K ord
      (by omega) (heads.2 ord) flipTop eight cap flipWidth flipRow d mass.2 mass.1 sIn
    rw [row_energy_colour_swap F.m F.n] at p;omega

#print axioms large_strict_source_one_list_escapes
end JSP452Audit.StarHost
