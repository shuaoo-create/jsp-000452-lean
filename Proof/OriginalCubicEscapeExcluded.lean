import CubicActualEscapePrice
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- Every possible degree-three region has now been excluded on its real
exterior. This lower bound applies to every minimal strict family. -/
theorem strict_source_degree_at_least_four (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank) :
    4≤diagonal F.n F.m (F.r+2)-1 := by
  let D := diagonal F.n F.m (F.r+2)-1
  have least : 3≤D := strict_source_degree_at_least_three F paid
  by_contra! less
  have three : D=3 := by omega
  obtain ⟨K⟩ := degreeRegion_exists F.G D
  let μ := matchingEdges (F.G.induce K.core)
  let a := K.roots.ncard
  let k := matchingEdges (F.G.induce K.rest)
  let d := F.rank-matchingEdges F.G
  obtain ⟨_,_,small,cap,_,_⟩ := minimal_rank_exact_source F paid
  have orig : matchingEdges F.G+d=F.rank := by dsimp [d];omega
  have split := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=a+μ+k at split
  have deficit : 2≤d := (minimal_strict_source_deficit F paid).2.2
  have top : diagonal F.n F.m (F.r+2)=4 := by dsimp [D] at three;omega
  have width := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  obtain ⟨lim,fees⟩ := (low_degree_original_costs F paid K).1 three
  have root : 3*minimumExposure F.G D+rootShortfall F.G K.roots D ≤2*highestWidth F.n F.m F.r+2 := by
    change 3*minimumExposure F.G D+(rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest)≤2*highestWidth F.n F.m F.r+2 at fees
    omega
  have strict := F.strict
  have outcomes := strict_cubic_escape_must_have_binary_overrun F paid K three
  have actual := strict_exterior_whole_tail_prices F paid K
  have inner := single_embedded_side_heads_below_degree F paid K
  rcases outcomes with ⟨red,blue,esc,over⟩|⟨blue,red,esc,over⟩
  · obtain ⟨rank,smaller,_,length,_,_⟩ := actual.1 esc
    change rowCount (F.s-μ) F.t (F.r+a)=k+d at rank
    change μ+a+F.r+d+1≤F.s at length
    have opp := inner.2 blue esc ⟨0,F.ht⟩
    have cost := cubic_actual_escape_paid F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G K three F.row F.live top red
      (by omega) over paid cap (by change 3≤F.s-μ;omega)
      (by change F.rank=rowCount (F.s-μ) F.t (F.r+a)+(a+μ);omega)
      smaller width lim root
    omega
  · obtain ⟨rank,smaller,_,length,_,_⟩ := actual.2 esc
    change rowCount F.s (F.t-μ) (F.r+a)=k+d at rank
    change μ+a+F.r+d+1≤F.t at length
    have opp := inner.1 red esc ⟨0,F.hs⟩
    have flip := swap_positive_forcing_row F.G _ _ F.row
    have same : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have tailSwap : rowCount (F.t-μ) F.s (F.r+a)=rowCount F.s (F.t-μ) (F.r+a) := by simp [rowCount,Nat.add_comm (F.t-μ) F.s]
    have hflip := highest_width_colour_swap F.m F.n F.r
    have cost := cubic_actual_escape_paid F.ht F.hs F.m F.n F.hm F.hn F.pm F.pn F.G K three flip
      (by rw [same];exact F.live) ((diagonal_swap _ _ _).trans top) blue (by omega) over
      (by rw [same];exact paid) cap (by change 3≤F.t-μ;omega)
      (by change rowCount F.t F.s F.r=rowCount (F.t-μ) F.s (F.r+a)+(a+μ);rw [same,tailSwap];omega)
      (by rw [same,tailSwap];exact smaller) (by rw [hflip];exact width) lim (by rw [hflip];exact root)
    rw [row_energy_colour_swap F.m F.n] at cost;omega

/-- Any failure of the original Ramsey equation would yield a
degree-at-least-four source satisfying the full escape classification. -/
theorem original_failure_needs_degree_four {s t : ℕ} (hs:0<s) (ht:0<t) (n:Fin s→ℕ) (m:Fin t→ℕ)
    (hn:Antitone n) (hm:Antitone m) (pn:∀i,1≤n i) (pm:∀j,1≤m j)
    (fail : sizeRamsey (forest n) (forest m)≠∑i∈Finset.Icc 2 (s+t),diagonal n m i) :
    ∃F:StrictFamily.{u},AllSmallerPaid.{u} F.rank ∧ 4≤diagonal F.n F.m (F.r+2)-1 ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → F.edges≤B.edges) ∧
      (∀B:StrictFamily.{u},B.rank=F.rank → B.edges=F.edges → F.order≤B.order) ∧
      ∀K:DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1),RemainingRegionCases F K := by
  obtain ⟨F,paid,edges,order,cases⟩ := original_failure_has_classified_regions.{u} hs ht n m hn hm pn pm fail
  exact ⟨F,paid,strict_source_degree_at_least_four F paid,edges,order,cases⟩

#print axioms strict_source_degree_at_least_four
#print axioms original_failure_needs_degree_four
end JSP452Audit.StarHost
