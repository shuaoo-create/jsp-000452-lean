import FourFullGreedyPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

private theorem at_original_degree {s t r D : ℕ} (hs : 0<s) (ht : 0<t)
    (n : Fin s→ℕ) (m : Fin t→ℕ) (hn : Antitone n) (hm : Antitone m) (pn : ∀i,1≤n i) (pm : ∀j,1≤m j)
    {X : Type*} [Finite X] (G : SimpleGraph X) (K : DegreeRegion G D) (four:D=4)
    (order : s≤t) (before : r<s) (head : n ⟨0,hs⟩=D) (top : diagonal n m (r+2)=D+1)
    (cap : ∀v,Nat.card (G.neighborSet v)≤D) (width : highestWidth n m r≤minimumExposure G D)
    (row : ForcingRow G s t (padDemand n) (padDemand m) r) (live : 0<rowCount s t r)
    (d : ℕ) (balance : matchingEdges G+d=rowCount s t r) (short : d<s)
    (exposed : 1≤minimumExposure G D) (deficit : minimumExposure G D+1≤d)
    (budget : 4*minimumExposure G D+(rootShortfall G K.roots D+2*(G.induce K.roots).edgeSet.ncard+
      crossCount G K.roots K.rest)≤2*highestWidth n m r+10)
    (red : WholeListRegionAlternative G K.core n d) (blue : WholeListRegionAlternative G K.core m d)
    (embedded : t≤matchingEdges (G.induce K.core)+d) (far : s+r+highestWidth n m r≤t)
    :
    rowEnergy n m r≤G.edgeSet.ncard := by
  subst D
  exact four_full_head_greedy_paid hs ht n m hn hm pn pm G K order before head top cap width row live d
    balance short exposed deficit budget red blue embedded far

/-- The double-embedded original branch is excluded in every degree at
least four, without any assumed domination theorem. -/
theorem strict_source_one_list_escapes_from_four (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (large : 4≤diagonal F.n F.m (F.r+2)-1) :
    matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)<max F.s F.t := by
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  by_cases five : 5≤D
  · exact strict_source_one_list_escapes_from_five F paid K five
  have four : D=4 := by change 4≤D at large;omega
  by_contra! both
  have axes := low_strict_original_axis F paid K (Or.inr four) both
  have mass := strict_source_whole_list_alternatives F K
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have strict := F.strict
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  obtain ⟨one,width⟩ := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have deficit := (minimal_strict_source_deficit F paid).2.1
  have costs := ((low_degree_original_costs F paid K).2.1 four).2
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨nL,mL⟩ := le_min_iff.mp (strict_source_strong_lengths F).1
  change F.r+d+1≤F.s at nL
  change F.r+d+1≤F.t at mL
  rcases le_total F.s F.t with ord|ord
  · obtain ⟨head,far,_⟩ := axes.1 ord
    have p := at_original_degree F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K four ord (by omega) head
      top cap width F.row F.live d balance (by omega) (one.trans width) deficit costs mass.1 mass.2 tr far
    omega
  · obtain ⟨head,far,_⟩ := axes.2 ord
    have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipH := highest_width_colour_swap F.m F.n F.r
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have flipLive : 0<rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using F.live
    have flipRow := swap_positive_forcing_row F.G (padDemand F.n) (padDemand F.m) F.row
    have p := at_original_degree F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K four ord (by omega) head
      flipTop cap (flipH.le.trans width) flipRow flipLive d flipRank (by omega) (one.trans width) deficit
      (by rw [flipH];exact costs) mass.2 mass.1 sr (by rw [flipH];exact far)
    rw [row_energy_colour_swap F.m F.n] at p;omega

#print axioms strict_source_one_list_escapes_from_four
end JSP452Audit.StarHost
