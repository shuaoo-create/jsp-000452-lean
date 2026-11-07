import StrictActualRootBudget
import RobustHalfOrderGap
namespace JSP452Audit.StarHost
universe u

/-- All costs here are measured on the same original region, including its
internal root edges. These are the three low-degree caps used for both lists. -/
theorem low_degree_original_costs (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) :
    let D := diagonal F.n F.m (F.r+2)-1
    let ρ := minimumExposure F.G D
    let h := highestWidth F.n F.m F.r
    let L := rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+crossCount F.G K.roots K.rest
    (D=3 → ρ≤2 ∧ 3*ρ+L≤2*h+2) ∧ (D=4 → ρ≤5 ∧ 4*ρ+L≤2*h+10) ∧
      (D=5 → ρ≤3 ∧ 3*ρ+L≤10 ∧ L≤7) := by
  intro D ρ h L
  obtain ⟨_,_,_,cap,_,_⟩ := minimal_rank_exact_source F paid
  have cert := strict_source_region_root_budget F paid K
  have cert' : D*ρ+L+2≤2*h+2*(D/2)*(D/2+1) := by
    change D*ρ+rootShortfall F.G K.roots D+2*(F.G.induce K.roots).edgeSet.ncard+
      crossCount F.G K.roots K.rest+2≤2*h+2*(D/2)*(D/2+1) at cert
    dsimp [L]; omega
  have limits := row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap
  change 1≤h ∧ h≤ρ at limits
  refine ⟨?_,?_,?_⟩
  · intro three;rw [three] at cert';omega
  · intro four;rw [four] at cert';omega
  · intro five;rw [five] at cert';omega

/-- The two original lengths simultaneously pay the opposite forest's
half-order and the rank of the actual exterior. -/
theorem double_embedded_length_guards (F : StrictFamily.{u}) {D : ℕ} (K : DegreeRegion F.G D)
    (short : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G))
    (less : matchingEdges F.G<F.rank) :
    let a := K.roots.ncard
    let μ := matchingEdges (F.G.induce K.core)
    let k := matchingEdges (F.G.induce K.rest)
    let d := F.rank-matchingEdges F.G
    let x := ∑i,(F.n i-1)/2
    let y := ∑j,(F.m j-1)/2
    k+a+2*d+2*y+F.r≤F.s ∧ k+a+2*d+2*x+F.r≤F.t ∧
      k+2*a+3*d+2*x+2*y+F.r≤a+μ+1 := by
  intro a μ k d x y
  obtain ⟨sIn,tIn⟩ := max_le_iff.mp short
  have halves := strict_source_whole_list_gap F K
  have A : F.s+d+2*x≤μ+1 := halves.1.resolve_left (by change F.s≤μ+d at sIn;omega)
  have B : F.t+d+2*y≤μ+1 := halves.2.resolve_left (by change F.t≤μ+d at tIn;omega)
  have part := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=a+μ+k at part
  have live := F.live
  have bal : a+μ+k+d+F.r+1=F.s+F.t := by
    change 0<rowCount F.s F.t F.r at live
    have eq : matchingEdges F.G+d=rowCount F.s F.t F.r := by change _=F.rank;dsimp [d];omega
    dsimp [rowCount] at live eq
    omega
  omega

#print axioms low_degree_original_costs
#print axioms double_embedded_length_guards
end JSP452Audit.StarHost
