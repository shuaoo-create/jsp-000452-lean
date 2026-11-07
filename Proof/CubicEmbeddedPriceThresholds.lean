import CubicOriginalHeightProfile
import LowDegreeRegionGuards
namespace JSP452Audit.StarHost
universe u

/-- The two price thresholds for a cubic embedded source. The first pays
mixed third columns and the second pays opposite-side pure winners. -/
theorem cubic_embedded_price_thresholds (F : StrictFamily.{u}) (paid : AllSmallerPaid.{u} F.rank)
    (K : DegreeRegion F.G (diagonal F.n F.m (F.r+2)-1)) (three : diagonal F.n F.m (F.r+2)-1=3)
    (both : max F.s F.t≤matchingEdges (F.G.induce K.core)+(F.rank-matchingEdges F.G)) :
    let h := highestWidth F.n F.m F.r
    F.rank+(∑i,F.n i)+(∑j,F.m j)+h≤F.G.edgeSet.ncard+2*F.r+2 ∧ 2*F.rank+2*h≤F.G.edgeSet.ncard := by
  intro h
  let D := diagonal F.n F.m (F.r+2)-1
  let d := F.rank-matchingEdges F.G
  let a := K.roots.ncard
  let μ := matchingEdges (F.G.induce K.core)
  let M := a+μ
  let k := matchingEdges (F.G.induce K.rest)
  let ρ := minimumExposure F.G D
  let ζ := rootShortfall F.G K.roots D
  let u := ∑i,F.n i
  let v := ∑j,F.m j
  let e := F.G.edgeSet.ncard
  obtain ⟨_,_,less,cap,_,_⟩ := minimal_rank_exact_source F paid
  have own := ordinary_region_original_edge_account F.G D cap K
  change 2*e+ζ=2*D*M+D*ρ+crossCount F.G K.roots K.rest+2*(F.G.induce K.rest).edgeSet.ncard at own
  have copyD : D=3 := three
  rw [copyD] at own
  have root := ((low_degree_original_costs F paid K).1 three).2
  change 3*ρ+(ζ+2*(F.G.induce K.roots).edgeSet.ncard+crossCount F.G K.roots K.rest)≤2*h+2 at root
  have ek : k≤(F.G.induce K.rest).edgeSet.ncard := matchingEdges_le_edgeCount _
  have floor : 3*M+k+3*ρ≤e+h+1 := by omega
  have part := region_rank_partition F.G K.barrier K.tight K.pieces
  change matchingEdges F.G=M+k at part
  have bal : F.rank=M+k+d := by dsimp [d];omega
  obtain ⟨sr,tr⟩ := max_le_iff.mp both
  have ⟨red,blue⟩ := strict_source_whole_list_alternatives F K
  have q := nontrivial_core_count_le_region_pieces F.G D K
  change nontrivialCoreCount (F.G.induce K.core)≤a+ρ at q
  obtain ⟨_,redM,_⟩ := red.resolve_left (by change ¬(μ+d+1≤F.s);change F.s≤μ+d at sr;omega)
  obtain ⟨_,blueM,_⟩ := blue.resolve_left (by change ¬(μ+d+1≤F.t);change F.t≤μ+d at tr;omega)
  change u+d≤μ+nontrivialCoreCount (F.G.induce K.core) at redM
  change v+d≤μ+nontrivialCoreCount (F.G.induce K.core) at blueM
  have uM : u+d≤M+ρ := by dsimp [M];omega
  have vM : v+d≤M+ρ := by dsimp [M];omega
  have guards := (double_embedded_length_guards F K both less).2.2
  change k+2*a+3*d+2*(∑i,(F.n i-1)/2)+2*(∑j,(F.m j-1)/2)+F.r≤M+1 at guards
  obtain ⟨_,deficit,two⟩ := minimal_strict_source_deficit F paid
  change ρ+1≤d at deficit
  change 2≤d at two
  have width := (row_minimum_exposure F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm F.G F.r F.live F.row cap).2
  change h≤ρ at width
  change F.rank+u+v+h≤e+2*F.r+2 ∧ 2*F.rank+2*h≤e
  omega

#print axioms cubic_embedded_price_thresholds
end JSP452Audit.StarHost
