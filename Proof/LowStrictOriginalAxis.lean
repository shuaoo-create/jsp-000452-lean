import LowEmbeddedOrderedAxis
namespace JSP452Audit.StarHost
universe u

/-- At either remaining degree the shorter original side has a full head,
the lengths differ by at least r+h, and its one-axis upper bound holds. -/
theorem low_strict_original_axis (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1))
    (low : diagonal F.n F.m (F.r+2)-1=3 ∨ diagonal F.n F.m (F.r+2)-1=4)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let h := highestWidth F.n F.m F.r
    let E := rowEnergy F.n F.m F.r
    (F.s≤F.t → F.n ⟨0,F.hs⟩=D ∧ F.s+F.r+h≤F.t ∧ E≤(F.t-1-F.r)*D+(∑i,F.n i)+h) ∧
    (F.t≤F.s → F.m ⟨0,F.ht⟩=D ∧ F.t+F.r+h≤F.s ∧ E≤(F.s-1-F.r)*D+(∑j,F.m j)+h) := by
  intro D h E
  let d := F.rank-matchingEdges F.G
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨one,width⟩ := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have deficit := (minimal_strict_source_deficit F paid).2.1
  have mass := strict_source_whole_list_alternatives F K
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  have costs := low_degree_original_costs F paid K
  have root3 (deg : D=3) : minimumExposure F.G D≤2 ∧
      3*minimumExposure F.G D+rootShortfall F.G K.roots D≤2*h+2 := by
    obtain ⟨small,part⟩ := costs.1 deg
    change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤2*h+2 at part
    exact ⟨small,by omega⟩
  have root4 (deg : D=4) : 4*minimumExposure F.G D+rootShortfall F.G K.roots D≤2*h+10 := by
    have part := (costs.2.1 deg).2
    change 4*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤2*h+10 at part
    omega
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  constructor
  · intro ord
    exact low_embedded_ordered_axis F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K low ord (by omega)
      (nc _) top cap width d balance (one.trans width) deficit root3 root4 mass.1 mass.2 tr F.strict
  · intro ord
    have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipH := highest_width_colour_swap F.m F.n F.r
    have flipE := row_energy_colour_swap F.m F.n F.r
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have ans := low_embedded_ordered_axis F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K low ord (by omega)
      (mc _) flipTop cap (flipH.le.trans width) d flipRank (one.trans width) deficit
      (by rw [flipH];exact root3) (by rw [flipH];exact root4) mass.2 mass.1 sr (by rw [flipE];exact F.strict)
    rw [flipH,flipE] at ans
    exact ans

#print axioms low_strict_original_axis
end JSP452Audit.StarHost
