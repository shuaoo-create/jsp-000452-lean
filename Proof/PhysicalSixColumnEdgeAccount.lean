import ActualSixthColumnSlotLoss
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem six_slot_saving_per_piece (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) :
    chosenSlots F.G T 3+T.card≤chosenSlots F.G T 2 := by
  have per (c) (mem:c∈T) : Nat.card c.supp/4+1≤Nat.card c.supp/3 := by
    obtain ⟨lo,order,_,_⟩ := strict_six_true_component_capacity F paid six c (actual c mem)
    omega
  have total := Finset.sum_le_sum (s:=T) (fun c mem => per c mem)
  rw [Finset.sum_add_distrib] at total
  simpa only [chosenSlots,Finset.sum_const,nsmul_eq_mul,Nat.cast_id,mul_one] using total

theorem six_column_edge_account (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (six:diagonal F.n F.m (F.r+2)-1=6) (T:Finset F.G.ConnectedComponent)
    (actual:∀c∈T,c∈oddRegularComponents F.G 6) (tax:ℕ→ℕ)
    (prices:∀j,2≤j → j≤6 → widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (componentVertices F.G T)ᶜ) j+tax j) :
    let U := componentVertices F.G T
    let P := matchingEdges (F.G.induce U)
    let d := F.rank-matchingEdges F.G
    5*P+3*T.card+1≤d+highestWidth F.n F.m F.r+∑q∈Finset.range 5,tax (q+2) := by
  intro U P d
  let O := F.G.induce Uᶜ
  have closed := component_vertices_closed F.G T
  have rank := closed_union_matching_split F.G U closed
  change matchingEdges F.G=P+matchingEdges O at rank
  let e : O⊕g F.G.induce U ≃g F.G := (regionSumIso F.G Set.univ Uᶜ U (Set.compl_union_self _) disjoint_compl_left
    (fun v hv w hw edge => hv (closed w hw v edge.symm))).trans (induceUnivIso F.G)
  have edges : (O⊕g F.G.induce U).edgeSet.ncard=F.G.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rw [edge_ncard_sumGraph] at edges
  have cost := (strict_six_chosen_component_columns F paid six T actual).2.1
  change (F.G.induce U).edgeSet.ncard=6*P+3*T.card at cost
  rw [cost] at edges
  have original := minimal_rank_exact_source F paid
  have earlier := original.2.1
  have less := original.2.2.1
  have sum : matchingEdges F.G+d=F.rank := by dsimp only [d];omega
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=6) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 6+highestWidth F.n F.m F.r at area
  have cover := (envelope_reserve_account O 5).1
  change envelopeReserve O 5+(matchingEdges O+interiorInventory O 6)=O.edgeSet.ncard at cover
  have paidColumns := Finset.sum_le_sum (s:=Finset.range 5) (fun q hq => prices (q+2) (by omega)
    (by have := Finset.mem_range.mp hq;omega))
  rw [Finset.sum_add_distrib] at paidColumns
  change interiorArea F.n F.m F.r 6 ≤ interiorInventory O 6+(∑q∈Finset.range 5,tax (q+2)) at paidColumns
  clear * - edges earlier sum rank area cover paidColumns
  omega

#print axioms six_slot_saving_per_piece
#print axioms six_column_edge_account
end JSP452Audit.StarHost
