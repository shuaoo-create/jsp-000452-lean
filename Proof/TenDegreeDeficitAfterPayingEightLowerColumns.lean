import TheTenthColumnOnTheSameRegularExterior
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

theorem ten_closed_exterior_column_budget (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (tax:ℕ→ℕ)
    (prices:∀j,2≤j → j≤10 → widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce (K.support)ᶜ) j+tax j) :
    let P := K.P
    let U := K.support
    10*P+5*K.eps+1≤matchingEdges (F.G.induce U)+(F.rank-matchingEdges F.G)+
      highestWidth F.n F.m F.r+(∑q∈Finset.range 9,tax (q+2)) := by
  intro P U
  let O := F.G.induce Uᶜ
  have closed := K.support_closed
  have rank := closed_union_matching_split F.G U closed
  change matchingEdges F.G=matchingEdges (F.G.induce U)+matchingEdges O at rank
  let e : O⊕g F.G.induce U ≃g F.G := (regionSumIso F.G Set.univ Uᶜ U (Set.compl_union_self _) disjoint_compl_left
    (fun v hv w hw edge => hv (closed w hw v edge.symm))).trans (induceUnivIso F.G)
  have edges : (O⊕g F.G.induce U).edgeSet.ncard=F.G.edgeSet.ncard := Nat.card_congr e.mapEdgeSet
  rw [edge_ncard_sumGraph] at edges
  have cost := K.fee
  change (F.G.induce U).edgeSet.ncard=10*P+5*K.eps at cost
  rw [cost] at edges
  obtain ⟨_,earlier,less,_,_,_⟩ := minimal_rank_exact_source F paid
  have area := original_area_by_height F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm (r:=F.r) (D:=10) (by omega) (by decide)
  change rowEnergy F.n F.m F.r=F.rank+interiorArea F.n F.m F.r 10+highestWidth F.n F.m F.r at area
  have cover := (envelope_reserve_account O 9).1
  change envelopeReserve O 9+(matchingEdges O+interiorInventory O 10)=O.edgeSet.ncard at cover
  have columns := Finset.sum_le_sum (s:=Finset.range 9) (fun q hq => prices (q+2) (by omega)
    (by have := Finset.mem_range.mp hq;omega))
  rw [Finset.sum_add_distrib] at columns
  change interiorArea F.n F.m F.r 10 ≤ interiorInventory O 10+(∑q∈Finset.range 9,tax (q+2)) at columns
  clear * - edges earlier less rank area cover columns
  omega


theorem ten_regular_exterior_slot_deficit (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank)
    (ten:diagonal F.n F.m (F.r+2)-1=10) (K:TenRegularBudget F.G) (z:ℕ)
    (redMax:∀i,F.n i+z≤11) (blueMax:∀j,F.m j+z≤11) :
    K.P+5*K.eps+2+K.slack≤(F.rank-matchingEdges F.G)+2*highestWidth F.n F.m F.r+chosenSlots F.G K.selected z := by
  let P := K.P
  let h := highestWidth F.n F.m F.r
  let M := chosenSlots F.G K.selected z
  let tax (j:ℕ) := if j=10 then M+(h-1) else P
  have original := strict_tenth_column_slot_tax F paid ten K.selected z redMax blueMax
  change widthAt F.n F.m F.r 10≤uniformEnvelope (F.G.induce K.supportᶜ) 10+M+(h-1) at original
  have prices (j:ℕ) (lo:2≤j) (_:j≤10) : widthAt F.n F.m F.r j≤uniformEnvelope (F.G.induce K.supportᶜ) j+tax j := by
    by_cases eq:j=10
    · subst j;simpa only [tax,if_pos rfl,Nat.add_assoc] using original
    · simpa only [tax,if_neg eq] using ten_closed_low_column_tax F paid ten K j (by omega)
  have budget := ten_closed_exterior_column_budget F paid ten K tax prices
  have total : (∑q∈Finset.range 9,tax (q+2))=8*P+M+(h-1) := by simp [Finset.sum_range_succ,tax];omega
  change 10*P+5*K.eps+1≤matchingEdges (F.G.induce K.support)+(F.rank-matchingEdges F.G)+h+_ at budget
  rw [total] at budget
  have rank : matchingEdges (F.G.induce K.support)≤P := K.fits
  have hp : 1≤h := (strict_ten_inventory F paid ten).1
  change P+5*K.eps+2+(P-matchingEdges (F.G.induce K.support))≤_+2*h+M
  omega

theorem ten_regular_slot_volume {X:Type u} [Finite X] {G:SimpleGraph X} (K:TenRegularBudget G) (z:ℕ) :
    (z+1)*chosenSlots G K.selected z≤2*K.P+K.eps := by
  have price := Finset.sum_le_sum (s:=K.selected) (fun c _ => Nat.mul_div_le (Nat.card c.supp) (z+1))
  have size := (component_union_accounts G K.selected).1
  change K.support.ncard=∑c∈K.selected,Nat.card c.supp at size
  rw [←size] at price
  change (z+1)*(∑c∈K.selected,Nat.card c.supp/(z+1))≤_
  rw [Finset.mul_sum];exact price.trans_eq K.order
#print axioms ten_closed_exterior_column_budget
#print axioms ten_regular_exterior_slot_deficit
#print axioms ten_regular_slot_volume
end JSP452Audit.StarHost
