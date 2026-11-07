import FiveFullEmbeddedOriginalPrice
namespace JSP452Audit.StarHost
universe u

/-- Every degree at least five now forces an actual escaping list at any
ordinary region of the original minimal-rank strict host. -/
theorem strict_source_one_list_escapes_from_five (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (large : 5≤diagonal F.n F.m (F.r+2)-1) :
    matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)<max F.s F.t := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  by_cases six : 6≤D
  · exact strict_source_one_list_escapes_from_six F paid K six
  have five : D=5 := by change 5≤D at large;omega
  by_contra! both
  have heads := five_embedded_shorter_head_attains F paid K five both
  have mass := strict_source_whole_list_alternatives F K
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have strict := F.strict
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  obtain ⟨one,width⟩ := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have deficit := (minimal_strict_source_deficit F paid).2.1
  have costs := ((low_degree_original_costs F paid K).2.2 five).2.1
  change 3*minimumExposure F.G D+
    (rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+crossCount F.G K.roots K.rest)≤10 at costs
  have budget : 3*minimumExposure F.G D+rootShortfall F.G K.roots D+crossCount F.G K.roots K.rest≤10 := by omega
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨nL,mL⟩ := le_min_iff.mp (strict_source_strong_lengths F).1
  change F.r+d+1≤F.s at nL
  change F.r+d+1≤F.t at mL
  rcases le_total F.s F.t with ord|ord
  · have p := five_matched_full_head_paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K five ord
      (by omega) ((heads.1 ord).trans five.symm) top cap width F.row F.live d balance
      (by omega) (one.trans width) deficit budget mass.1 mass.2 tr
    omega
  · have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipWidth := (highest_width_colour_swap F.m F.n F.r).le.trans width
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have flipLive : 0<rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using F.live
    have flipRow := swap_positive_forcing_row F.G (padDemand F.n) (padDemand F.m) F.row
    have p := five_matched_full_head_paid F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K five ord
      (by omega) ((heads.2 ord).trans five.symm) flipTop cap flipWidth flipRow flipLive d flipRank
      (by omega) (one.trans width) deficit budget mass.2 mass.1 sr
    rw [row_energy_colour_swap F.m F.n] at p;omega

#print axioms strict_source_one_list_escapes_from_five
end JSP452Audit.StarHost
