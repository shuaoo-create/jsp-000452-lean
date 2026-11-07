import PersistentRegionPrice
namespace JSP452Audit.StarHost
universe u

/-- On the same strict source, any original head reaching the cap requires
the opposite length to lie at most at the persistent core/root threshold. -/
theorem strict_full_head_needs_root_core_capacity (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    (F.n ⟨0,F.hs⟩=D → F.t≤μ+K.roots.ncard+F.r) ∧
    (F.m ⟨0,F.ht⟩=D → F.s≤μ+K.roots.ncard+F.r) := by
  intro D μ
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have large : 3≤D := strict_source_degree_at_least_three F paid
  have exposure := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  change highestWidth F.n F.m F.r≤minimumExposure F.G D at exposure
  have strict := F.strict
  constructor
  · intro head
    by_contra! wide
    have pay := persistent_region_price F.hs F.ht F.G F.n F.m F.hn F.hm F.pn F.pm F.row F.live
      D rfl large head cap K wide
    omega
  · intro head
    by_contra! wide
    have swapped : 0<rowCount F.t F.s F.r := by simpa [rowCount,Nat.add_comm F.t F.s] using F.live
    have deg : D=diagonal F.m F.n (F.r+2)-1 := by rw [diagonal_swap F.m F.n]
    have pay := persistent_region_price F.ht F.hs F.G F.m F.n F.hm F.hn F.pm F.pn
      (swap_positive_forcing_row F.G _ _ F.row) swapped D deg large head cap K wide
    rw [row_energy_colour_swap F.m F.n,highest_width_colour_swap F.m F.n] at pay
    omega

/-- A full head and a nonembedded opposite side together consume at least
d+1 distinct roots of the actual ordinary region. -/
theorem strict_full_head_root_lower (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    let d := F.rank-matchingEdges F.G
    (F.n ⟨0,F.hs⟩=D → μ<F.t → d+1≤K.roots.ncard) ∧
    (F.m ⟨0,F.ht⟩=D → μ<F.s → d+1≤K.roots.ncard) := by
  intro D μ d
  obtain ⟨p,q⟩ := strict_full_head_needs_root_core_capacity F paid K
  obtain ⟨b,r⟩ := strict_source_erased_tail_lengths F paid K
  constructor
  · intro head live;have lower := b live;have upper := p head
    change μ+F.r+d+1≤F.t at lower;change F.t≤μ+K.roots.ncard+F.r at upper;omega
  · intro head live;have lower := r live;have upper := q head
    change μ+F.r+d+1≤F.s at lower;change F.s≤μ+K.roots.ncard+F.r at upper;omega

#print axioms strict_full_head_needs_root_core_capacity
#print axioms strict_full_head_root_lower
end JSP452Audit.StarHost
