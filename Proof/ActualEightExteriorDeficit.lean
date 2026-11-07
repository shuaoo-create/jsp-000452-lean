import OddRegularUnionOrderAndRank
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem eight_exterior_column_budget (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (tax:ℕ→ℕ)
    (prices:∀j,2≤j → j≤8 → widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+tax j) :
    let P := ∑c∈T,Nat.card c.supp/2
    let U := componentVertices F.G T
    8*P+4*T.card+1≤matchingEdges (F.G.induce U)+(F.rank-matchingEdges F.G)+
      highestWidth F.n F.m F.r+(∑q∈Finset.range 7,tax (q+2)) := by
  intro P U
  let O := F.G.induce Uᶜ
  have closed := component_vertices_closed F.G T
  have rank := closed_union_matching_split F.G U closed
  change matchingEdges F.G=matchingEdges (F.G.induce U)+matchingEdges O at rank
  let e : O⊕g F.G.induce U ≃g F.G := (regionSumIso F.G Set.univ Uᶜ U (Set.compl_union_self _) disjoint_compl_left
    (fun v hv w hw edge => hv (closed w hw v edge.symm))).trans (induceUnivIso F.G)
  have edges : (O⊕g F.G.induce U).edgeSet.ncard=F.G.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rw [edge_ncard_sumGraph] at edges
  have cost := (regular_union_at_even_degree F.G 4 T actual).2.1
  change (F.G.induce U).edgeSet.ncard=8*P+4*T.card at cost
  rw [cost] at edges
  obtain ⟨_,earlier,less,_,_,_⟩ := minimal_rank_exact_source F paid
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=8) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 8+highestWidth F.n F.m F.r at area
  have cover := (envelope_reserve_account O 7).1
  change envelopeReserve O 7+(matchingEdges O+interiorInventory O 8)=O.edgeSet.ncard at cover
  have columns := Finset.sum_le_sum (s:=Finset.range 7) (fun q hq => prices (q+2) (by omega)
    (by have := Finset.mem_range.mp hq;omega))
  rw [Finset.sum_add_distrib] at columns
  change interiorArea F.n F.m F.r 8 ≤ interiorInventory O 8+(∑q∈Finset.range 7,tax (q+2)) at columns
  clear * - edges earlier less rank area cover columns
  omega

theorem eight_exterior_deficit_by_slots (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (eight:diagonal F.n F.m (F.r+2)-1=8) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 8) (few:T.card≤2) (z:ℕ)
    (redMax:∀i,F.n i+z≤9) (blueMax:∀j,F.m j+z≤9) :
    let P := ∑c∈T,Nat.card c.supp/2
    let U := componentVertices F.G T
    let d := F.rank-matchingEdges F.G
    P+4*T.card+2+(P-matchingEdges (F.G.induce U))≤
      d+2*highestWidth F.n F.m F.r+chosenSlots F.G T z := by
  intro P U d
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G T z
  let tax (j:ℕ) := if j=8 then M+(h-1) else P
  have original := strict_eighth_column_slot_tax F paid eight T z redMax blueMax
  have prices (j:ℕ) (lo:2≤j) (_:j≤8) : widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce Uᶜ) j+tax j := by
    by_cases eq:j=8
    · subst j;simpa [tax,M,h,U,Nat.add_assoc] using original
    · simpa [tax,eq,P] using strict_eight_low_column_tax F paid eight T actual few j (by omega)
  have budget := eight_exterior_column_budget F paid eight T actual tax prices
  have total : (∑q∈Finset.range 7,tax (q+2))=6*P+M+(h-1) := by simp [Finset.sum_range_succ,tax];omega
  change 8*P+4*T.card+1≤matchingEdges (F.G.induce U)+d+h+_ at budget
  rw [total] at budget
  have rank := (regular_union_at_even_degree F.G 4 T actual).2.2.1
  change matchingEdges (F.G.induce U)≤P at rank
  have hp : 1≤h := (strict_eight_inventory F paid eight).1
  change _≤d+2*h+M
  omega

#print axioms eight_exterior_column_budget
#print axioms eight_exterior_deficit_by_slots
end JSP452Audit.StarHost
