import FullHeadActualMixedBoundary
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

/-- A full original head forces an actual offending red two-leaf
against some blue threshold. When f2 fits in the core matching budget,
the entire overrun occurs at the unique height b+1. -/
theorem strict_full_mixed_boundary (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let μ := matchingEdges (F.G.induce K.core)
    (F.n ⟨0,F.hs⟩=D → FullMixedBoundary F.n F.m F.ht F.r D μ) ∧
    (F.m ⟨0,F.ht⟩=D → FullMixedBoundary F.m F.n F.hs F.r D μ) := by
  intro D μ
  let d := F.rank-matchingEdges F.G
  let ρ := minimumExposure F.G D
  have deg : 4≤D := strict_source_degree_at_least_four F paid
  have top : diagonal F.n F.m (F.r+2)=D+1 := by dsimp [D] at *;omega
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  have res : ρ+1≤d := (minimal_strict_source_deficit F paid).2.1
  have endp := original_root_endpoint_guards F paid K
  have one := strict_full_head_unique_escape F paid K
  obtain ⟨_,z,zlt,miss,lower⟩ := strict_mixed_columns_exceed_exposure F paid K
  constructor
  · intro full
    have len := (one.1 full).2.1
    change μ+K.roots.ncard+F.r+d+1≤F.s at len
    have guard := endp.1
    change K.roots.ncard+F.r+2*(d+∑i,(F.n i-1)/2)≤F.t at guard
    exact full_head_forces_mixed_boundary F.n F.m F.hs F.ht F.hn F.hm F.pn F.pm full top ρ μ width (by omega)
      (by omega) ⟨z,zlt,miss,lower⟩
  · intro full
    have len := (one.2 full).2.1
    change μ+K.roots.ncard+F.r+d+1≤F.t at len
    have guard := endp.2
    change K.roots.ncard+F.r+2*(d+∑i,(F.m i-1)/2)≤F.s at guard
    have swap : rowCount F.t F.s F.r=F.rank := by simp [StrictFamily.rank,rowCount,Nat.add_comm F.t F.s]
    have mono : monochromeHeight F.m F.n (F.r+z)=monochromeHeight F.n F.m (F.r+z) := by unfold monochromeHeight;apply max_comm
    exact full_head_forces_mixed_boundary F.m F.n F.ht F.hs F.hm F.hn F.pm F.pn full ((diagonal_swap _ _ _).trans top)
      ρ μ ((highest_width_colour_swap _ _ _).le.trans width) (by omega) (by omega)
      ⟨z,by rw [swap];exact zlt,by rw [mono,diagonal_swap];exact miss,by rw [diagonal_swap F.m F.n,diagonal_swap F.m F.n];exact lower⟩

#print axioms strict_full_mixed_boundary
end JSP452Audit.StarHost
