import CubicOppositeBinary
import FullPrefixCornerPrice
namespace JSP452Audit.StarHost
universe u

/-- Both orientations of the same strict cubic source must now have a
three-leaf shorter head, a two-leaf opposite head and the exact 3/2 peak. -/
theorem strict_cubic_binary_axis (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (three : diagonal F.n F.m (F.r+2)-1=3)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    let h := highestWidth F.n F.m F.r
    (F.s≤F.t → F.n ⟨0,F.hs⟩=3 ∧ F.m ⟨0,F.ht⟩=2 ∧
      originalThresholdCount F.n 3+originalThresholdCount F.m 2=h+F.r+1) ∧
    (F.t≤F.s → F.m ⟨0,F.ht⟩=3 ∧ F.n ⟨0,F.hs⟩=2 ∧
      originalThresholdCount F.m 3+originalThresholdCount F.n 2=h+F.r+1) := by
  intro h
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  have axes := low_strict_original_axis F paid K (Or.inl three) both
  have mass := strict_source_whole_list_alternatives F K
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  have balance : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have deficit := (minimal_strict_source_deficit F paid).2.1
  have root := ((low_degree_original_costs F paid K).1 three).2
  change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
    crossCount F.G K.roots K.rest)≤2*h+2 at root
  have budget : 3*minimumExposure F.G D+rootShortfall F.G K.roots D≤2*h+2 := by omega
  obtain ⟨nr,mr⟩ := strict_row_range F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.row F.strict
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  constructor
  · intro ord
    obtain ⟨head,far,_⟩ := axes.1 ord
    refine ⟨head.trans three,?_⟩
    exact cubic_ordered_opposite_binary F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K three ord (by omega)
      head (mc _) top F.live cap width d balance deficit budget mass.2 tr far F.strict
  · intro ord
    obtain ⟨head,far,_⟩ := axes.2 ord
    have flipTop := (diagonal_swap F.m F.n (F.r+2)).trans top
    have flipH := highest_width_colour_swap F.m F.n F.r
    have flipRank : matchingEdges F.G+d=rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using balance
    have flipLive : 0<rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.s F.t] using F.live
    have p := cubic_ordered_opposite_binary F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K three ord
      (by omega) head (nc _) flipTop flipLive cap (flipH.le.trans width) d flipRank deficit
      (by rw [flipH];exact budget) mass.1 sr (by rw [flipH];exact far)
      (by rw [row_energy_colour_swap F.m F.n];exact F.strict)
    rw [flipH] at p
    exact ⟨head.trans three,p⟩

#print axioms strict_cubic_binary_axis
end JSP452Audit.StarHost
