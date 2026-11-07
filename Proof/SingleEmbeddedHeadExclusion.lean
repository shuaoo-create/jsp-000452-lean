import OriginalCapRowPrice
namespace JSP452Audit.StarHost
universe u

/-- In a single-empty region, every head on the embedded side is strictly
below D, in either orientation of the same minimal source. -/
theorem single_embedded_side_heads_below_degree (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    (F.s≤μ → μ<F.t → ∀i,F.n i<D) ∧ (F.t≤μ → μ<F.s → ∀j,F.m j<D) := by
  intro D μ
  let d := F.rank-matchingEdges F.G
  let h := highestWidth F.n F.m F.r
  have large : 3≤D := strict_source_degree_at_least_three F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  change h≤minimumExposure F.G D at width
  have debt := (minimal_strict_source_deficit F paid).2.1
  change minimumExposure F.G D+1≤d at debt
  obtain ⟨_,_,payBlue,payRed⟩ := strict_source_paid_erased_core_successors F paid K
  obtain ⟨lenBlue,lenRed⟩ := strict_source_erased_tail_lengths F paid K
  obtain ⟨redCap,blueCap⟩ := minimal_original_head_cap F paid
  have strict := F.strict
  constructor
  · intro embed live i
    have length : μ+F.r+d+1≤F.t := lenBlue live
    have bound : F.n ⟨0,F.hs⟩≤D := redCap _
    have small : F.n ⟨0,F.hs⟩<D := by
      by_contra! bad
      have head : F.n ⟨0,F.hs⟩=D := by omega
      obtain ⟨_,_,_,_,_,_,smaller⟩ := payBlue live
      have yes := head_at_cap_erasure_pays F.hs F.ht F.G F.n F.m F.hn F.hm F.pm head top
        (show F.s+F.r+highestWidth F.n F.m F.r≤F.t by change F.s+F.r+h≤F.t;omega)
        (by omega) cap K width (by change F.r<F.t-μ;omega) smaller
      omega
    exact lt_of_le_of_lt (F.hn (show (⟨0,F.hs⟩ : Fin F.s)≤ i from Nat.zero_le _)) small
  · intro embed live j
    have length : μ+F.r+d+1≤F.s := lenRed live
    have bound : F.m ⟨0,F.ht⟩≤D := blueCap _
    have small : F.m ⟨0,F.ht⟩<D := by
      by_contra! bad
      have head : F.m ⟨0,F.ht⟩=D := by omega
      obtain ⟨_,_,_,_,_,_,smaller⟩ := payRed live
      rw [row_energy_colour_swap] at smaller
      have swapWidth : highestWidth F.m F.n F.r=h := highest_width_colour_swap _ _ _
      have flip : diagonal F.m F.n (F.r+2)=D+1 := (diagonal_swap _ _ _).trans top
      have yes := head_at_cap_erasure_pays F.ht F.hs F.G F.m F.n F.hm F.hn F.pn head flip
        (by rw [swapWidth];omega) (by omega) cap K (swapWidth ▸ width) (by change F.r<F.s-μ;omega) smaller
      rw [row_energy_colour_swap] at yes
      omega
    exact lt_of_le_of_lt (F.hm (show (⟨0,F.ht⟩ : Fin F.t)≤ j from Nat.zero_le _)) small

#print axioms single_embedded_side_heads_below_degree
end JSP452Audit.StarHost
