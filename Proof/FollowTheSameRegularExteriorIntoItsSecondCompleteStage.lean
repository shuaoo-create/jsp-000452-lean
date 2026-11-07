import TheCompleteFirstRegularStageBoundsBothTheOriginalColumnAndItsExteriorExposure
open private JSP452Audit.StarHost.degree_on_independent_full_set from ExteriorWholeForestStep
namespace JSP452Audit.StarHost
open SimpleGraph
universe u

set_option maxHeartbeats 600000 in
theorem regular_block_second_stage (F:StrictFamily.{u}) (paid:AllSmallerPaid.{u} F.rank) {p:ℕ} (B:RegularOddBlock F.G p)
    (degree:diagonal F.n F.m (F.r+2)-1=2*p) (head:max (F.n ⟨0,F.hs⟩) (F.m ⟨0,F.ht⟩)+3=2*p)
    (one:highestWidth F.n F.m F.r=1) :
    let O := B.outside
    let b := peakCountAbove O (2*p-1)
    let c := peakCountAbove O (2*p-2)
    minimumExposure (O.induce (peakPrefix O b)ᶜ) (2*p-1)≤p ∧
      minimumExposure (O.induce (peakPrefix O c)ᶜ) (2*p-2)≤p+2 ∧ widthAt F.n F.m F.r (2*p)≤b+B.P+p-3 := by
  intro O b c
  let C := B.inside
  let S := peakPrefix O b
  let T := peakPrefix O c
  let W := additionalLabels S T
  have many : 6≤p := by have d := strict_source_degree_at_least_eleven F paid;omega
  obtain ⟨A,stage,_,row,small,net,bounds,first,peak,length⟩ := regular_block_first_stage F paid p B degree head one
  refine ⟨first,?_,length⟩
  let C₁ := C.induce Aᶜ
  let J := O.induce Sᶜ⊕g C₁
  let r := F.r+b+A.ncard
  change ForcingRow J F.s F.t (padDemand F.n) (padDemand F.m) r at row
  change J.edgeSet.ncard≤rowEnergy F.n F.m r at net
  change rowCount F.s F.t r<F.rank at small
  change ∀v,Nat.card (J.neighborSet v)≤2*p-1 at bounds
  change widthAt F.n F.m r (2*p)≤p-2 at peak
  have reg (v:B.piece.supp) : Nat.card (C.neighborSet v)=2*p := (component_degree_eq F.G B.piece v).trans (B.full.2 _ v.property)
  have innerCap (v:↥(Aᶜ:Set B.piece.supp)) : Nat.card (C₁.neighborSet v)≤2*p-1 := by
    have h := complete_stage_lowers_cap C (2*p) A (fun v => (reg v).le) stage v
    change Nat.card (C₁.neighborSet v)<2*p at h;omega
  obtain ⟨V,inside⟩ := complete_degree_stage_exists C₁ (2*p-1)
  obtain ⟨before,_,_,size,fee,⟨iso⟩⟩ := peak_history_second_stage O (2*p) (by omega)
  change W.ncard=c-b at size
  change (O.induce Sᶜ).edgeSet.ncard=(O.induce Tᶜ).edgeSet.ncard+(2*p-1)*(c-b) at fee
  change (O.induce Sᶜ).induce Wᶜ ≃g O.induce Tᶜ at iso
  have sum := sum_after_both_deletions (O.induce Sᶜ) C₁ W V _ _ (pad_antitone F.n F.hn) (pad_antitone F.m F.hm)
    (pad_positive F.n F.pn) (pad_positive F.m F.pm) row
  let Y := O.induce Tᶜ⊕g C₁.induce Vᶜ
  let k := W.ncard+V.ncard
  have next := forcingRow_of_iso (Iso.sumCongr iso (Iso.refl : C₁.induce Vᶜ ≃g C₁.induce Vᶜ)) sum
  rw [Nat.add_assoc r W.ncard V.ncard] at next
  change ForcingRow Y F.s F.t (padDemand F.n) (padDemand F.m) (r+k) at next
  have payInner := JSP452Audit.StarHost.degree_on_independent_full_set C₁ V (2*p-1) inside.2.1 inside.1
  have sale : J.edgeSet.ncard=Y.edgeSet.ncard+(2*p-1)*k := by
    dsimp only [J,Y,k];rw [edge_ncard_sumGraph,edge_ncard_sumGraph,Nat.mul_add,size];omega
  have tax : rowEnergy F.n F.m r≤rowEnergy F.n F.m (r+k)+(2*p-1)*k+(p-2) := by
    by_cases live:0<rowCount F.s F.t r
    · have height := live_row_height_at_degree_cap J F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm row live bounds
      have pr := prefix_at_degree_cap F.hs F.ht F.n F.m F.hn F.hm r k (2*p-1) height
      rw [show 2*p-1+1=2*p by omega] at pr;omega
    · have zero : rowEnergy F.n F.m r=0 := by simp only [rowEnergy,show rowCount F.s F.t r=0 by omega,Finset.range_zero,Finset.sum_empty]
      omega
  have fee2 : Y.edgeSet.ncard≤rowEnergy F.n F.m (r+k)+(p-2) := by omega
  have loOuter := (exact_peak_inventory_cut O (2*p-2)).2
  have loInner := complete_stage_lowers_cap C₁ (2*p-1) V innerCap inside
  have cap2 := sum_vertex_degree_cap (O.induce Tᶜ) (C₁.induce Vᶜ) (2*p-2) loOuter
    (fun v => by have h := loInner v;omega)
  have smaller : rowCount F.s F.t (r+k)<F.rank := by dsimp only [rowCount] at small ⊢;omega
  have result := even_stage_low_surplus Y F.hs F.ht F.n F.m F.hn F.hm F.pn F.pm next smaller paid cap2 many fee2
  dsimp only [Y] at result
  rw [minimumExposure_sumGraph] at result
  change minimumExposure (O.induce Tᶜ) (2*p-2)≤_;omega

#print axioms regular_block_second_stage
end JSP452Audit.StarHost
