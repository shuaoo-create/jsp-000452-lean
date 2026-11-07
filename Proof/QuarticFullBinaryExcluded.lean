import QuarticFullBinaryActualPayment
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- In degree four a full escaping side cannot face a binary opposite
side. All possible heads in that orientation therefore reduce to three. -/
theorem strict_quartic_opposite_must_be_three (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (four : diagonal F.n F.m (F.r+2)-1=4) :
    (F.n ⟨0,F.hs⟩=4 → F.m ⟨0,F.ht⟩=3) ∧
    (F.m ⟨0,F.ht⟩=4 → F.n ⟨0,F.hs⟩=3) := by
  let D := diagonal F.n F.m (F.r+2)-1
  let μ := matchingEdges (F.G.induce K.core)
  let d := F.rank-matchingEdges F.G
  let a := K.roots.ncard
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,small,cap,_,_⟩ := minimal_rank_exact_source F paid
  have rank : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  have res := (minimal_strict_source_deficit F paid).2.1
  obtain ⟨lim,root⟩ := (low_degree_original_costs F paid K).2.1 four
  have cost : 4*minimumExposure F.G D+rootShortfall F.G K.roots D≤2*highestWidth F.n F.m F.r+10 := by
    change 4*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤2*highestWidth F.n F.m F.r+10 at root;omega
  have unique := strict_full_head_unique_escape F paid K
  have guards := original_root_endpoint_guards F paid K
  have outer := strict_exterior_endpoint_guards F paid K
  have mass := strict_source_whole_list_alternatives F K
  have data := strict_both_complete_exteriors F paid K
  have trigger := strict_full_mixed_boundary F paid K
  obtain ⟨nc,mc⟩ := minimal_original_head_cap F paid
  have live := F.live
  obtain ⟨i,j,_,eq⟩ := diagonal_attained F.n F.m F.hs F.ht F.r (by dsimp [rowCount] at live;omega)
  have ncap := nc i
  have mcap := mc j
  have ns := F.hn (show (⟨0,F.hs⟩:Fin F.s) ≤ i from Nat.zero_le _)
  have ms := F.hm (show (⟨0,F.ht⟩:Fin F.t) ≤ j from Nat.zero_le _)
  have bad := F.strict
  constructor
  · intro head
    have full := head.trans four.symm
    obtain ⟨embedded,len,_,other⟩ := unique.1 full
    change μ+a+F.r+d+1≤F.s at len
    have escaped : μ<F.s := by omega
    change F.t≤μ at embedded
    have opp := other ⟨0,F.ht⟩
    by_contra! no
    have two : F.m ⟨0,F.ht⟩=2 := by omega
    have half := (mass.2.resolve_left (by change ¬μ+d+1≤F.t;omega)).1
    change F.t+d+2*(∑j,(F.m j-1)/2)≤μ+1 at half
    have ext := outer.1 escaped
    change a+F.r+2*(d+_)+_≤F.s-μ at ext
    have fee := quartic_full_binary_paid F.G K F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm four cap F.live full two top d rank
      (data.1 escaped) escaped (by change F.t+d≤μ+1;omega) guards.1
      (by change a+F.r+2*d≤F.s-μ;omega) width res cost lim (trigger.1 full)
    omega
  · intro head
    have full := head.trans four.symm
    obtain ⟨embedded,len,_,other⟩ := unique.2 full
    change μ+a+F.r+d+1≤F.t at len
    have escaped : μ<F.t := by omega
    change F.s≤μ at embedded
    have opp := other ⟨0,F.hs⟩
    by_contra! no
    have two : F.n ⟨0,F.hs⟩=2 := by omega
    have half := (mass.1.resolve_left (by change ¬μ+d+1≤F.s;omega)).1
    change F.s+d+2*(∑i,(F.n i-1)/2)≤μ+1 at half
    have ext := outer.2 escaped
    change a+F.r+2*(d+_)+_≤F.t-μ at ext
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have H := highest_width_colour_swap F.m F.n F.r
    have fee := quartic_full_binary_paid F.G K F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn four cap (by rw [swap];exact F.live) full
      two ((diagonal_swap _ _ _).trans top) d (rank.trans swap.symm) (by rw [swap];exact data.2 escaped) escaped
      (by change F.s+d≤μ+1;omega) guards.2 (by change a+F.r+2*d≤F.t-μ;omega)
      (by rw [H];exact width) res (by rw [H];exact cost) lim (trigger.2 full)
    rw [row_energy_colour_swap F.m F.n] at fee;omega

#print axioms strict_quartic_opposite_must_be_three
end JSP452Audit.StarHost
